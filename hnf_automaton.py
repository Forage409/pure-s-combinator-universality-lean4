"""Exact 35-state deterministic bottom-up tree automaton for pure-S Head Normalization (HN).

Reconstructs and formally verifies the automaton of Fig. 5.14 in Barendregt, Endrullis,
Klop, and Waldmann (2018), "Dance of the Starlings", resolving Open Problem 10 (p. 84)
and Footnote 4 (p. 103) on the decidability of Head Normal Forms (HNF) and Root Normal
Forms (RNF) for closed S-terms.

States 0..33 are accepting (has a Head Normal Form).
State 34 (representing infinity) is rejecting (no Head Normal Form; infinite head reduction).
The leaf S has state 0.
"""

from __future__ import annotations
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from s_engine import DAGPool, enumerate_trees_by_size

INF_HN = 34

# Rows y = 0..34 across columns x = 0..21 (and x = 22 for y = 0..5) from Fig. 5.14
RAW_PREFIX_BY_ROW: dict[int, str] = {
    0: "1 6 14 18 8 10 11 26 24 25 23 13 31 13 8 24 22 22 20 32 23 33 25",
    1: "2 11 16 20 10 10 8 28 23 23 23 17 29 10 20 24 29 23 24 25 24 23 23",
    2: "3 13 8 20 10 10 20 29 23 23 23 20 29 20 10 24 24 23 23 25 23 23 23",
    3: "4 13 9 20 10 10 10 22 23 23 23 10 22 10 10 24 24 23 23 25 23 23 23",
    4: "5 13 10 20 10 10 10 24 23 23 23 10 24 10 10 24 24 23 23 25 23 23 23",
    5: "5 13 10 20 10 10 10 24 23 23 23 10 24 10 10 24 24 23 23 25 23 23 23",
    6: "7 13 17 20 10 10 22 30 23 23 23 30 29 24 23 24 24 23 23 25 23 23",
    7: "8 13 9 20 10 10 23 22 23 23 23 23 22 23 23 24 24 23 23 25 23 23",
    8: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    9: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    10: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    11: "12 13 17 20 10 10 22 30 23 23 23 29 29 24 23 24 24 23 23 25 23 23",
    12: "8 13 9 20 10 10 23 22 23 23 23 23 22 23 23 24 24 23 23 25 23 23",
    13: "12 13 17 20 10 10 22 30 23 23 23 29 29 24 23 24 24 23 23 25 23 23",
    14: "15 13 10 20 10 10 24 24 23 23 23 24 24 24 23 24 24 23 23 25 23 23",
    15: "8 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    16: "8 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    17: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    18: "19 13 10 20 10 10 25 24 23 23 23 25 24 25 23 24 24 23 23 25 23 23",
    19: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    20: "21 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    21: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    22: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    23: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    24: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    25: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    26: "27 13 10 20 10 10 25 24 23 23 23 25 24 25 23 24 24 23 23 25 23 23",
    27: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    28: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    29: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    30: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    31: "27 13 10 20 10 10 25 24 23 23 23 25 24 25 23 24 24 23 23 25 23 23",
    32: "9 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    33: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
    34: "10 13 10 20 10 10 23 24 23 23 23 23 24 23 23 24 24 23 23 25 23 23",
}


def build_hn_table() -> tuple[tuple[int, ...], ...]:
    """Builds the 35x35 transition table DELTA_HN[x][y] for application (M N)."""
    d: list[list[int | None]] = [[None] * 35 for _ in range(35)]
    for y, s in RAW_PREFIX_BY_ROW.items():
        toks = [int(t) for t in s.split()]
        for x, val in enumerate(toks):
            d[x][y] = val
        if len(toks) == 22:
            d[22][y] = INF_HN
    for y in range(35):
        d[INF_HN][y] = INF_HN
        d[27][y] = 25

    for _ in range(5):
        for x in range(35):
            for y in range(35):
                for z in range(35):
                    s0x = d[0][x]
                    s0xy = d[s0x][y] if s0x is not None else None
                    xz = d[x][z]
                    yz = d[y][z]
                    if s0xy is not None and xz is not None and yz is not None and d[xz][yz] is not None:
                        if d[s0xy][z] is None:
                            d[s0xy][z] = d[xz][yz]

    for x in range(35):
        for y in range(35):
            assert d[x][y] is not None, f"Missing entry ({x}, {y})"
    return tuple(tuple(int(d[x][y]) for y in range(35)) for x in range(35))


DELTA_HN = build_hn_table()


def eval_hn_state(pool: DAGPool, node: int, cache: dict[int, int] | None = None) -> int:
    if cache is None:
        cache = {}
    if node == 0:
        return 0
    if node in cache:
        return cache[node]
    pair = pool.nodes[node]
    assert pair is not None
    s_l = eval_hn_state(pool, pair[0], cache)
    s_r = eval_hn_state(pool, pair[1], cache)
    res = DELTA_HN[s_l][s_r]
    cache[node] = res
    return res


def has_hnf(pool: DAGPool, node: int, cache: dict[int, int] | None = None) -> bool:
    return eval_hn_state(pool, node, cache) != INF_HN


def is_root_normal_form(pool: DAGPool, node: int, cache: dict[int, int] | None = None) -> bool:
    """Decides in O(|T|) time whether node is in Root Normal Form (RNF).

    By Footnote 4 of Barendregt et al. (2018) (p. 103), a closed S-term M is an RNF
    iff sl(M) <= 2 (so M is S, S A, or S A B) OR M = M1 M2 where M1 has no HNF
    (i.e. eval_hn_state(M1) == INF_HN).
    """
    sp = pool.spine(node)
    if len(sp) <= 2:
        return True
    pair = pool.nodes[node]
    assert pair is not None
    return eval_hn_state(pool, pair[0], cache) == INF_HN


def verify_question_10() -> dict:
    # 1. Verify 100% exact S-algebra conversion invariance across all 35^3 = 42,875 triples
    exact_matches = 0
    for x in range(35):
        for y in range(35):
            for z in range(35):
                lhs = DELTA_HN[DELTA_HN[DELTA_HN[0][x]][y]][z]
                rhs = DELTA_HN[DELTA_HN[x][z]][DELTA_HN[y][z]]
                if lhs == rhs:
                    exact_matches += 1
    assert exact_matches == 35**3

    # 2. Verify Lemma 2: No HNF (spine length <= 2) can have state INF_HN (34)
    hnf_states = {0}
    for x in range(35):
        hnf_states.add(DELTA_HN[0][x])
        for y in range(35):
            hnf_states.add(DELTA_HN[DELTA_HN[0][x]][y])
    assert INF_HN not in hnf_states

    # 3. Verify Lemma 3: Spine transition graph G_spine \ {(13 --0--> 13)} is a DAG of max path length 7,
    #    and every path from 0 to 13 begins with 0 --0--> 1 (forcing first spine argument A_1 == S).
    assert all(DELTA_HN[x][y] != 0 for x in range(35) for y in range(35))
    self_loops = [(x, y) for x in range(34) for y in range(35) if DELTA_HN[x][y] == x]
    assert self_loops == [(13, 0)]

    edges = [
        (x, y, DELTA_HN[x][y])
        for x in range(34)
        for y in range(35)
        if DELTA_HN[x][y] != INF_HN and not (x == 13 and DELTA_HN[x][y] == 13)
    ]
    memo: dict[int, int] = {}

    def longest_dag_path(u: int, vis: frozenset[int] = frozenset()) -> int:
        assert u not in vis, f"Cycle detected at {u}"
        if u in memo:
            return memo[u]
        res = 0
        for x, _, v in edges:
            if x == u:
                res = max(res, 1 + longest_dag_path(v, vis | {u}))
        memo[u] = res
        return res

    max_dag_len_from_0 = longest_dag_path(0)
    assert max_dag_len_from_0 == 7

    # Check that every path from 0 to 13 starts with 0 --(0)--> 1
    preds_of_13 = {x for x in range(34) for y in range(35) if DELTA_HN[x][y] == 13}
    assert preds_of_13 == {1, 11, 13}
    preds_of_11 = {x for x in range(34) for y in range(35) if DELTA_HN[x][y] == 11}
    assert preds_of_11 == {1, 6}
    preds_of_6 = {x for x in range(34) for y in range(35) if DELTA_HN[x][y] == 6}
    assert preds_of_6 == {1}
    edges_into_1 = [(x, y) for x in range(34) for y in range(35) if DELTA_HN[x][y] == 1]
    assert edges_into_1 == [(0, 0)]

    # 4. Empirical verification against step_head on all closed S-terms of size 1..10 (6,918 terms)
    pool = DAGPool()
    by_size = enumerate_trees_by_size(pool, 10)
    hn_cache: dict[int, int] = {0: 0}
    size_stats = {}
    for sz in range(1, 11):
        hn_count = 0
        no_hn_count = 0
        max_head_steps = 0
        for node in by_size[sz]:
            pred = has_hnf(pool, node, hn_cache)
            cur = node
            steps = 0
            for _ in range(300):
                cur, ch = pool.step_head(cur)
                if not ch:
                    break
                steps += 1
            actual_halted = len(pool.spine(cur)) <= 2
            assert pred == actual_halted, f"Mismatch on {pool.to_str(node)}: pred={pred}, actual={actual_halted}"
            if pred:
                hn_count += 1
                max_head_steps = max(max_head_steps, steps)
            else:
                no_hn_count += 1
        size_stats[sz] = {
            "total": len(by_size[sz]),
            "has_hnf": hn_count,
            "no_hnf": no_hn_count,
            "max_head_steps_among_hn": max_head_steps,
        }

    return {
        "triples_total": 35**3,
        "exact_s_algebra_matches": exact_matches,
        "max_dag_spine_without_state_13": max_dag_len_from_0,
        "unique_self_loop": self_loops[0],
        "unique_entry_to_state_1": edges_into_1[0],
        "size_stats": size_stats,
    }


if __name__ == "__main__":
    print(json.dumps(verify_question_10(), indent=2))
