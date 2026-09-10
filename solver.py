# -*- coding: utf-8 -*-
"""
圆桌排座求解器（纯 Python 标准库）

两阶段约束求解：
  阶段 A：把人员分配到桌（处理桌容量、固定桌位、必须分桌等硬性约束；
          用分支定界最大化“希望同桌”满足数）
  阶段 B：对每一桌做环形座位排列（处理固定座位、禁止相邻等硬约束；
          最大化“希望相邻”满足数）

无解时返回一个极小冲突约束集合（朴素最小不满足子集），
前端可让用户停用其中任一约束后重算。
"""

import sys
import time

sys.setrecursionlimit(20000)

# 规则类型
WISH_SAME = "wish_same"          # 希望同桌（软）
MUST_SEP = "must_separate"       # 必须分桌（硬）
WISH_ADJ = "wish_adjacent"       # 希望相邻（软）
FORBID_ADJ = "forbid_adjacent"   # 禁止相邻（硬）

SOFT_TYPES = (WISH_SAME, WISH_ADJ)
HARD_TYPES = (MUST_SEP, FORBID_ADJ)


class SolveError(Exception):
    """输入数据本身的问题（不是约束冲突），如桌子不存在、引用了不存在的人。"""


def solve(payload, time_budget=8.0):
    """求解入口。

    payload:
      tables:   [{id, name, seats}]
      people:   [{id, name}]
      rules:    [{id, type, a, b, disabled}]
      fixed:    {person_id: {"table": table_id, "seat": idx}}  # 用户指定的固定桌位
      locked:   {person_id: {"table": table_id, "seat": idx}}  # 用户在页面上锁定的座位
    返回 dict:
      成功: {status:"ok", seating:{pid:[tid,seat]}, score, totals, used_seats}
      无解: {status:"unsat", conflicts:[{kind,label,...}], reason}
      输入错: 抛出 SolveError
    """
    m = _build_model(payload)
    deadline = time.time() + time_budget

    # 先尝试完整优化求解
    result = _group_search(m, deadline, optimize=True)
    if result is not None:
        return _ok_result(m, result)

    if time.time() >= deadline:
        # 时间不够时，再给一点时间只找可行解
        result = _group_search(m, deadline + 2.0, optimize=False)
        if result is not None:
            return _ok_result(m, result)

    # 判定：究竟是“真无解”，还是只是搜索超时？
    feas_deadline = time.time() + 3.0
    result = _group_search(m, feas_deadline, optimize=False)
    if result is not None:
        return _ok_result(m, result)

    # 真无解 —— 找冲突约束组合
    conflicts = _find_conflicts(m, feas_deadline + 4.0)
    return {
        "status": "unsat",
        "conflicts": conflicts,
        "reason": "硬性约束相互冲突或座位不足，不存在可行排法。",
    }


# --------------------------------------------------------------------------
# 模型构建
# --------------------------------------------------------------------------

def _build_model(payload):
    tables_raw = payload.get("tables") or []
    people_raw = payload.get("people") or []
    rules_raw = payload.get("rules") or []
    fixed_raw = payload.get("fixed") or {}
    locked_raw = payload.get("locked") or {}

    if not isinstance(tables_raw, list) or not isinstance(people_raw, list):
        raise SolveError("数据格式错误：tables / people 应为数组")

    # 去重桌子 id
    tables = []
    tid_set = set()
    for t in tables_raw:
        tid = str(t.get("id"))
        if tid in tid_set:
            continue
        tid_set.add(tid)
        seats = _to_int(t.get("seats"), 0)
        tables.append({
            "id": tid,
            "name": str(t.get("name") or ("桌" + str(len(tables) + 1))),
            "seats": max(0, seats),
        })
    tid_index = {t["id"]: i for i, t in enumerate(tables)}

    people = []
    pid_set = set()
    for p in people_raw:
        pid = str(p.get("id"))
        if pid in pid_set:
            continue
        pid_set.add(pid)
        people.append({"id": pid, "name": str(p.get("name") or pid)})
    pid_index = {p["id"]: i for i, p in enumerate(people)}

    # 有效规则
    rules = []
    for r in rules_raw:
        rid = str(r.get("id"))
        rtype = r.get("type")
        a, b = str(r.get("a")), str(r.get("b"))
        if rtype not in (WISH_SAME, MUST_SEP, WISH_ADJ, FORBID_ADJ):
            continue
        if a not in pid_index or b not in pid_index or a == b:
            continue
        rules.append({
            "id": rid,
            "type": rtype,
            "a": pid_index[a],
            "b": pid_index[b],
            "disabled": bool(r.get("disabled")),
        })

    # 锚点：固定(fixed)优先于锁定(locked)；同位置的 fixed+locked 视为一致
    anchors = [None] * len(people)        # (桌索引, 座位索引或None)
    anchor_kinds = {}                     # 人员索引 -> {"fixed":bool,"lock":bool}

    def _apply_anchor(pid_s, data, kind):
        if pid_s not in pid_index:
            raise SolveError("固定座位引用了不存在的参与者：%s" % pid_s)
        if not isinstance(data, dict):
            return
        tid_s = str(data.get("table"))
        if tid_s not in tid_index:
            raise SolveError("固定座位引用了不存在的桌子：%s" % tid_s)
        ti = tid_index[tid_s]
        seat = data.get("seat")
        si = _to_int(seat, -1) if seat is not None else None
        if si is not None and not (0 <= si < tables[ti]["seats"]):
            # 座位越界（如桌位数被调小）——作为冲突报出
            si = -1
        pi = pid_index[pid_s]
        rec = anchor_kinds.setdefault(pi, {"fixed": False, "lock": False})
        rec[kind] = True
        if anchors[pi] is None:
            anchors[pi] = [ti, si]
        elif anchors[pi][0] != ti or (si is not None and anchors[pi][1] is not None
                                      and anchors[pi][1] != si):
            anchors[pi] = ["conflict", (ti, si)]  # 标记，稍后生成冲突

    for pid_s, data in (fixed_raw or {}).items():
        _apply_anchor(pid_s, data, "fixed")
    for pid_s, data in (locked_raw or {}).items():
        _apply_anchor(pid_s, data, "lock")

    n = len(people)

    # 约束边集合
    hard_sep = {}        # (i,j) -> [rule_id]  必须分桌
    forbid_adj = {}      # (i,j) -> [rule_id]  禁止相邻（同桌时）
    wish_same = {}       # (i,j) -> count      希望同桌
    wish_adj = {}        # (i,j) -> count      希望相邻
    soft_info = []       # [rule_id...] 软规则，用于总分
    for r in rules:
        if r["disabled"]:
            continue
        key = (min(r["a"], r["b"]), max(r["a"], r["b"]))
        if r["type"] == MUST_SEP:
            hard_sep.setdefault(key, []).append(r["id"])
        elif r["type"] == FORBID_ADJ:
            forbid_adj.setdefault(key, []).append(r["id"])
        elif r["type"] == WISH_SAME:
            wish_same[key] = wish_same.get(key, 0) + 1
            soft_info.append(r["id"])
        else:
            wish_adj[key] = wish_adj.get(key, 0) + 1
            soft_info.append(r["id"])

    # 规则文字标签（冲突展示用）
    def _pname(i):
        return people[i]["name"]

    rule_label = {}
    for r in rules:
        if r["disabled"]:
            continue
        tname = {WISH_SAME: "希望同桌", MUST_SEP: "必须分桌",
                 WISH_ADJ: "希望相邻", FORBID_ADJ: "禁止相邻"}[r["type"]]
        rule_label[r["id"]] = "%s：%s / %s" % (tname, _pname(r["a"]), _pname(r["b"]))

    model = {
        "tables": tables,
        "people": people,
        "rules": rules,
        "anchors": anchors,
        "anchor_kinds": anchor_kinds,
        "hard_sep": hard_sep,
        "forbid_adj": forbid_adj,
        "wish_same": wish_same,
        "wish_adj": wish_adj,
        "soft_info": soft_info,
        "rule_label": rule_label,
        "n": n,
    }

    # ---- 结构性预检：直接生成冲突，无需搜索 ----
    structural = _structural_conflicts(model)
    model["structural"] = structural
    return model


def _structural_conflicts(m):
    T = m["tables"]
    n = m["n"]
    out = []

    if n > sum(t["seats"] for t in T):
        out.append({
            "kind": "capacity",
            "label": "总座位不足：共 %d 人，但全部桌子只有 %d 个座位"
                     % (n, sum(t["seats"] for t in T)),
        })

    # 固定/锁定 互相矛盾、座位越界、同座位重复
    seat_occ = {}   # (桌, 座位) -> [(人, kind, label)]
    for pi, anc in enumerate(m["anchors"]):
        if anc is None:
            continue
        kinds = m["anchor_kinds"][pi]
        if anc[0] == "conflict":
            ti, si = anc[1]
            out.append({
                "kind": "anchor_clash",
                "label": "%s 的固定桌位与锁定桌位不一致" % m["people"][pi]["name"],
                "items": [_anchor_item(m, pi, "fixed"),
                          _anchor_item(m, pi, "lock")],
            })
            continue
        ti, si = anc
        t = T[ti]
        if si == -1:
            out.append({
                "kind": "bad_seat",
                "label": "%s 的固定座位超出「%s」的座位数（%d 座）"
                         % (m["people"][pi]["name"], t["name"], t["seats"]),
                "items": [_anchor_item(m, pi, "fixed" if kinds["fixed"] else "lock")],
            })
            continue
        if si is not None:
            seat_occ.setdefault((ti, si), []).append((pi, kinds))

    for (ti, si), occ in seat_occ.items():
        if len(occ) > 1:
            items = []
            for pi, kinds in occ:
                items.append(_anchor_item(m, pi, "fixed" if kinds["fixed"] else "lock"))
            out.append({
                "kind": "seat_taken",
                "label": "「%s」%d 号座位被多人固定：%s"
                         % (T[ti]["name"], si + 1,
                            "、".join(m["people"][pi]["name"] for pi, _ in occ)),
                "items": items,
            })

    # 锚点导致的分桌违规、单桌超载
    table_anchor_count = [0] * len(T)
    for pi, anc in enumerate(m["anchors"]):
        if anc is None or anc[0] == "conflict" or anc[1] == -1:
            continue
        table_anchor_count[anc[0]] += 1
    for ti, t in enumerate(T):
        if table_anchor_count[ti] > t["seats"]:
            out.append({
                "kind": "table_overflow",
                "label": "「%s」只有 %d 座，但已有 %d 人固定/锁定在该桌"
                         % (t["name"], t["seats"], table_anchor_count[ti]),
            })

    for (i, j), rids in m["hard_sep"].items():
        ai, aj = m["anchors"][i], m["anchors"][j]
        if (ai and aj and ai[0] != "conflict" and aj[0] != "conflict"
                and ai[1] != -1 and aj[1] != -1 and ai[0] == aj[0]):
            out.append({
                "kind": "rule",
                "rule_id": rids[0],
                "label": m["rule_label"][rids[0"]] + "（两人已被固定在同一桌）",
            })

    # 固定座位上的禁止相邻
    for (i, j), rids in m["forbid_adj"].items():
        ai, aj = m["anchors"][i], m["anchors"][j]
        if (ai and aj and ai[0] == aj[0] and ai[0] != "conflict"
                and ai[1] is not None and aj[1] is not None
                and ai[1] != -1 and aj[1] != -1):
            sz = T[ai[0]]["seats"]
            if _adjacent(ai[1], aj[1], sz):
                out.append({
                    "kind": "rule",
                    "rule_id": rids[0],
                    "label": m["rule_label"][rids[0]] + "（两人固定座位相邻）",
                })

    # 去重
    seen = set()
    uniq = []
    for c in out:
        key = c.get("rule_id") or (c["kind"], c["label"])
        if key in seen:
            continue
        seen.add(key)
        uniq.append(c)
    return uniq


def _anchor_item(m, pi, kind):
    return {"person": m["people"][pi]["id"], "kind": kind,
            "label": ("固定座位" if kind == "fixed" else "锁定座位")
                     + "：" + m["people"][pi]["name"]}


def _adjacent(s1, s2, size):
    if size <= 1:
        return False
    diff = abs(s1 - s2)
    return diff == 1 or diff == size - 1


def _to_int(v, default):
    try:
        return int(v)
    except (TypeError, ValueError):
        return default


# --------------------------------------------------------------------------
# 阶段 A：人员 → 桌 的分组搜索
# --------------------------------------------------------------------------

def _person_order(m):
    """有锚点的人最先；其余按约束数量（度数）降序。"""
    n = m["n"]
    degree = [0] * n
    for (i, j), w in m["wish_same"].items():
        degree[i] += w
        degree[j] += w
    for (i, j), w in m["wish_adj"].items():
        degree[i] += w
        degree[j] += w
    for (i, j) in m["hard_sep"]:
        degree[i] += 1
        degree[j] += 1
    for (i, j) in m["forbid_adj"]:
        degree[i] += 1
        degree[j] += 1

    def key(i):
        anc = m["anchors"][i]
        anchored = 0 if (anc and anc[0] != "conflict") else 1
        return (anchored, -degree[i], i)

    return sorted(range(n), key=key)


def _group_search(m, deadline, optimize):
    if m["structural"]:
        return None

    T = m["tables"]
    k = len(T)
    n = m["n"]
    if k == 0:
        return None if n > 0 else {"groups": [], "seating": {}, "score": 0}

    order = _person_order(m)
    # 锚点人员预先落位
    group_of = [-1] * n
    counts = [0] * k
    same_now = 0   # 当前已满足的 wish_same 数（每条规则计一次）
    adj_now = 0    # 当前已“同组”的 wish_adj 对数（阶段A的乐观部分）

    for pi in order:
        anc = m["anchors"][pi]
        if anc is not None:
            group_of[pi] = anc[0]
            counts[anc[0]] += 1
            for (x, y), w in m["wish_same"].items():
                other = y if x == pi else (x if y == pi else -1)
                if other >= 0 and group_of[other] == anc[0]:
                    same_now += w
            for (x, y), w in m["wish_adj"].items():
                other = y if x == pi else (x if y == pi else -1)
                if other >= 0 and group_of[other] == anc[0]:
                    adj_now += w

    free_idx = 0
    while free_idx < n and group_of[order[free_idx]] != -1:
        free_idx += 1

    # wish_same / wish_adj 总权重（阶段 A 上界用）
    total_same = sum(m["wish_same"].values())
    total_adj = sum(m["wish_adj"].values())

    best = {"score": -1, "seating": None, "groups": None}
    nodes = [0]
    # 阶段B总体上界的乐观估计：同组的 wish_adj 视为都能相邻
    # （B 阶段实际不满足的部分在 leaf 处扣减）

    def upper_bound():
        return same_now + adj_now + (total_same - same_lost[0]) * 0 + (
            same_now + adj_now + remaining_same[0] + remaining_adj[0])

    # 未放置人员之间尚未实现的软边数（上界：都能满足）
    # 用增量维护 remaining_same / remaining_adj
    remaining_same = [total_same - same_now]
    remaining_adj = [total_adj - adj_now]
    # 因分桌已确定不可能满足的边
    same_lost = [0]
    adj_lost = [0]

    def edge_weights(pi, edges):
        res = {}
        for (x, y), w in edges.items():
            if x == pi:
                res[y] = res.get(y, 0) + w
            elif y == pi:
                res[x] = res.get(x, 0) + w
        return res

    sep_map = {}
    for (x, y) in m["hard_sep"]:
        sep_map.setdefault(x, set()).add(y)
        sep_map.setdefault(y, set()).add(x)

    def recurse(depth, same_now_v, adj_now_v, rem_same, rem_adj, lost_same, lost_adj):
        if (nodes[0] & 2047) == 0 and time.time() >= deadline:
            return
        nodes[0] += 1

        if depth == n:
            # 可行分组 → 阶段 B 排座
            groups = [[] for _ in range(k)]
            for pi in range(n):
                groups[group_of[pi]].append(pi)
            seating = [None] * n
            score = same_now_v
            ok = True
            total_adj_gain = 0
            for ti, members in enumerate(groups):
                if not members:
                    continue
                r = _seat_table(m, ti, members, group_of, seating,
                                deadline, optimize)
                if r is None:
                    ok = False
                    break
                total_adj_gain += r
            if not ok:
                return
            score += total_adj_gain
            if score > best["score"]:
                best["score"] = score
                best["seating"] = seating[:]
                best["groups"] = [g[:] for g in groups]
            return

        pi = order[depth]
        if group_of[pi] != -1:
            recurse(depth + 1, same_now_v, adj_now_v,
                    rem_same, rem_adj, lost_same, lost_adj)
            return

        # 候选桌
        forbidden = sep_map.get(pi, ())
        cands = []
        for ti in range(k):
            if counts[ti] >= T[ti]["seats"]:
                continue
            if any(group_of[q] == ti for q in forbidden):
                continue
            gain_s = 0
            gain_a = 0
            for (x, y), w in m["wish_same"].items():
                q = y if x == pi else (x if y == pi else -1)
                if q >= 0 and group_of[q] == ti:
                    gain_s += w
            for (x, y), w in m["wish_adj"].items():
                q = y if x == pi else (x if y == pi else -1)
                if q >= 0 and group_of[q] == ti:
                    gain_a += w
            cands.append((ti, gain_s, gain_a))

        # 启发式：偏好收益高的桌优先
        cands.sort(key=lambda c: -(2 * c[1] + c[2]))

        # 该人员涉及的软边（用于维护“剩余/损失”计数）
        my_same = edge_weights(pi, m["wish_same"])
        my_adj = edge_weights(pi, m["wish_adj"])

        for ti, gain_s, gain_a in cands:
            # 放置后更新：与尚未放置者之间的边从 remaining 移除；
            # 若被分到与对方（已放置）不同桌则计 lost（对方放置时已统计过，
            # 这里只需统计当前边中对方尚未放置、将来可能不同桌的上界——
            # 简化处理：remaining 只在两人都未放置时保留，上界保持有效）
            new_rem_s = rem_same
            new_rem_a = rem_adj
            for q, w in my_same.items():
                if group_of[q] == -1:
                    new_rem_s -= w
            for q, w in my_adj.items():
                if group_of[q] == -1:
                    new_rem_a -= w

            if optimize:
                # 乐观上界 = 当前已得 + 剩余待定边全部满足
                ub = same_now_v + gain_s + adj_now_v + gain_a + new_rem_s + new_rem_a
                if ub <= best["score"]:
                    continue

            group_of[pi] = ti
            counts[ti] += 1
            recurse(depth + 1, same_now_v + gain_s, adj_now_v + gain_a,
                    new_rem_s, new_rem_a, lost_same, lost_adj)
            counts[ti] -= 1
            group_of[pi] = -1

    recurse(0, same_now, adj_now, remaining_same[0], remaining_adj[0], 0, 0)

    if best["seating"] is None:
        return None
    seating = {}
    for pi, v in enumerate(best["seating"]):
        seating[m["people"][pi]["id"]] = [m["tables"][v[0]]["id"], v[1]]
    return {"groups": best["groups"], "seating": seating, "score": best["score"]}


# --------------------------------------------------------------------------
# 阶段 B：单桌环形排座
# --------------------------------------------------------------------------

def _seat_table(m, ti, members, group_of, out_seating, deadline, optimize):
    """返回该桌 wish_adj 最大满足数；不可行返回 None。结果写入 out_seating[pi]。"""
    T = m["tables"]
    size = T[ti]["seats"]
    memberset = set(members)

    # 固定座位（座位号确定的锚点）
    fixed = {}   # seat -> person
    anchored_persons = set()
    for pi in members:
        anc = m["anchors"][pi]
        if anc is not None and anc[0] == ti and anc[1] is not None and anc[1] != -1:
            fixed[anc[1]] = pi
            anchored_persons.add(pi)

    # 同桌成员间的禁止相邻 / 希望相邻（聚合权重与规则id）
    na_hard = {}
    adj_w = {}
    for (x, y), rids in m["forbid_adj"].items():
        if x in memberset and y in memberset:
            na_hard[(x, y)] = rids
    for (x, y), w in m["wish_adj"].items():
        if x in memberset and y in memberset:
            adj_w[(x, y)] = w

    # 固定座位之间预检查
    for (x, y) in na_hard:
        if x in anchored_persons and y in anchored_persons:
            sx = m["anchors"][x][1]
            sy = m["anchors"][y][1]
            if _adjacent(sx, sy, size):
                return None

    remaining = [pi for pi in members if pi not in anchored_persons]
    # 约束多的人先放
    def deg(pi):
        d = 0
        for (x, y) in na_hard:
            if x == pi or y == pi:
                d += 2
        for (x, y), w in adj_w.items():
            if x == pi or y == pi:
                d += w
        return d
    remaining.sort(key=lambda pi: (-deg(pi), pi))

    seat_of = [-1] * m["n"]
    occ = [False] * size
    init_score = 0
    for s, pi in fixed.items():
        seat_of[pi] = s
        occ[s] = True
    # 初始已相邻的 wish_adj
    for (x, y), w in adj_w.items():
        if x in anchored_persons and y in anchored_persons:
            if _adjacent(seat_of[x], seat_of[y], size):
                init_score += w

    total_adj = sum(adj_w.values())
    best_score = [-1]
    best_arr = [None]
    nodes = [0]

    def seat_ok(pi, s, current_score):
        # 硬约束：禁止相邻
        for (x, y) in na_hard:
            q = y if x == pi else (x if y == pi else -1)
            if q >= 0 and seat_of[q] >= 0 and _adjacent(s, seat_of[q], size):
                return False
        return True

    def recurse(idx, score_v, adj_done):
        if (nodes[0] & 2047) == 0 and time.time() >= deadline:
            return
        nodes[0] += 1

        if idx == len(remaining):
            if score_v > best_score[0]:
                best_score[0] = score_v
                best_arr[0] = seat_of[:]
            return

        pi = remaining[idx]

        # 与 pi 相关、尚未“定型”的 wish_adj 总权重（乐观上界）
        def my_remaining_weight():
            w_left = 0
            for (x, y), w in adj_w.items():
                q = y if x == pi else (x if y == pi else -1)
                if q >= 0 and seat_of[q] == -1 and q != pi:
                    w_left += w
            return w_left

        if optimize:
            ub = score_v + my_remaining_weight() + (total_adj - adj_done - my_remaining_weight()) * 0
            # 更稳妥的全量乐观上界：
            ub = score_v + (total_adj - adj_done)
            if ub <= best_score[0]:
                return

        # 选座位：按放上后即时相邻收益排序
        seat_choices = []
        for s in range(size):
            if occ[s]:
                continue
            if not seat_ok(pi, s, score_v):
                continue
            gain = 0
            for (x, y), w in adj_w.items():
                q = y if x == pi else (x if y == pi else -1)
                if q >= 0 and seat_of[q] >= 0 and _adjacent(s, seat_of[q], size):
                    gain += w
            seat_choices.append((-gain, s, gain))
        seat_choices.sort()

        for _, s, gain in seat_choices:
            # adj_done：以 pi 为其中一端、另一端已放置的边视为定型
            done_here = 0
            for (x, y), w in adj_w.items():
                q = y if x == pi else (x if y == pi else -1)
                if q >= 0 and seat_of[q] >= 0:
                    done_here += w
            occ[s] = True
            seat_of[pi] = s
            recurse(idx + 1, score_v + gain, adj_done + done_here)
            seat_of[pi] = -1
            occ[s] = False

    recurse(0, init_score, init_score)

    if best_arr[0] is None:
        return None
    arr = best_arr[0]
    for pi in members:
        if arr[pi] < 0:
            return None
        out_seating[pi] = (ti, arr[pi])
    return best_score[0]


# --------------------------------------------------------------------------
# 冲突诊断（极小不满足约束子集）
# --------------------------------------------------------------------------

def _find_conflicts(m, deadline):
    structural = m["structural"]
    if structural:
        return _with_actions(m, structural)

    # 可停用的候选约束：硬规则 + 锚点
    candidates = []   # (kind, key, label, disable_info)
    for r in m["rules"]:
        if r["disabled"]:
            continue
        if r["type"] in HARD_TYPES:
            candidates.append(("rule", r["id"], m["rule_label"][r["id"]],
                                {"rule_id": r["id"]}))
    for pi, anc in enumerate(m["anchors"]):
        if anc is None or anc[0] == "conflict":
            continue
        kinds = m["anchor_kinds"][pi]
        kind = "fixed" if kinds["fixed"] else "lock"
        label = ("固定座位" if kind == "fixed" else "锁定座位") + "：" + m["people"][pi]["name"]
        candidates.append(("anchor", (kind, pi), label,
                           {"person": m["people"][pi]["id"], "kind": kind}))

    # 逐个尝试停用：找到一个能让问题变可行的停用集合（朴素删除式 MUS）
    active = set(range(len(candidates)))

    def feasible_without(removed):
        sub = _copy_model_without(m, removed, candidates)
        if sub["structural"]:
            return False
        dl = min(time.time() + 1.2, deadline)
        return _group_search(sub, dl, optimize=False) is not None

    if not feasible_without(set()):
        pass  # 已知无解
    else:
        return [{"kind": "unknown",
                 "label": "搜索时间内未能找到可行排法，但也无法确定具体冲突；可尝试增大求解时间或简化约束。"}]

    # 删除式：尝试删除每一项，若删除后仍无解，则永久删除（不属于必需项）
    mus_indices = []
    removed = set()
    for idx in range(len(candidates)):
        if time.time() >= deadline:
            break
        trial = removed | {idx}
        if not feasible_without(trial):
            removed.add(idx)   # 删了它还是无解 → 它不是冲突核心
    mus = [i for i in range(len(candidates)) if i not in removed]

    # 只保留仍能复现无解的集合，输出冲突项
    conflicts = []
    for i in mus:
        kind, key, label, info = candidates[i]
        item = {"kind": kind, "label": label}
        item.update(info)
        conflicts.append(item)
    if not conflicts:
        conflicts = [{"kind": "unknown",
                      "label": "约束过于复杂，未能在限定时间内定位最小冲突；请尝试逐条停用规则排查。"}]
    return _with_actions(m, conflicts)


def _with_actions(m, conflicts):
    for c in conflicts:
        if c["kind"] == "rule":
            c.setdefault("action", {"type": "disable_rule", "rule_id": c.get("rule_id")})
        elif c["kind"] in ("fixed", "lock", "anchor"):
            c.setdefault("action", {"type": "clear_anchor",
                                    "person": c.get("person"),
                                    "anchor_kind": c.get("kind")})
        elif c["kind"] in ("anchor_clash", "seat_taken", "bad_seat"):
            # 多项目冲突：允许停用其中一个锚点
            for it in c.get("items", []):
                it.setdefault("action", {"type": "clear_anchor",
                                         "person": it.get("person"),
                                         "anchor_kind": it.get("kind")})
        # capacity / table_overflow：没有“停用一项”的对象，仅提示
    return conflicts


def _copy_model_without(m, removed, candidates):
    """构造一个停用了若干候选约束的模型副本（轻量）。"""
    disabled_rules = set()
    clear_anchors = set()      # person index
    for idx in removed:
        kind, key, label, info = candidates[idx]
        if kind == "rule":
            disabled_rules.add(key)
        else:
            anchor_kind, pi = key
            # fixed 与 lock 同时存在时，只清一种可能仍残留另一种 —— 两种都清
            clear_anchors.add(pi)

    rules = []
    for r in m["rules"]:
        r2 = dict(r)
        if r["id"] in disabled_rules:
            r2["disabled"] = True
        rules.append(r2)

    anchors = [(None if pi in clear_anchors else a)
               for pi, a in enumerate(m["anchors"])]

    hard_sep = {}
    forbid_adj = {}
    wish_same = {}
    wish_adj = {}
    rule_label = {}
    for r in rules:
        if r["disabled"]:
            continue
        key = (min(r["a"], r["b"]), max(r["a"], r["b"]))
        if r["type"] == MUST_SEP:
            hard_sep.setdefault(key, []).append(r["id"])
        elif r["type"] == FORBID_ADJ:
            forbid_adj.setdefault(key, []).append(r["id"])
        elif r["type"] == WISH_SAME:
            wish_same[key] = wish_same.get(key, 0) + 1
        else:
            wish_adj[key] = wish_adj.get(key, 0) + 1
        rule_label[r["id"]] = m["rule_label"].get(r["id"], r["id"])

    sub = dict(m)
    sub.update({
        "rules": rules,
        "anchors": anchors,
        "hard_sep": hard_sep,
        "forbid_adj": forbid_adj,
        "wish_same": wish_same,
        "wish_adj": wish_adj,
        "rule_label": rule_label,
    })
    sub["structural"] = _structural_conflicts(sub)
    return sub


# --------------------------------------------------------------------------

def _ok_result(m, result):
    total_s = sum(m["wish_same"].values())
    total_a = sum(m["wish_adj"].values())
    soft_total = len(m["soft_info"])
    used = {}
    for pid, pos in result["seating"].items():
        used[pos[0]] = used.get(pos[0], 0) + 1
    return {
        "status": "ok",
        "seating": result["seating"],
        "score": result["score"],
        "totals": {"soft": soft_total,
                   "wish_same": total_s,
                   "wish_adj": total_a},
        "used_seats": used,
    }
