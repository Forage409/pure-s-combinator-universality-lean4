"""Exact 39-state deterministic bottom-up tree automaton for pure-S strong normalization.

From Johannes Waldmann (2000), "The Combinator S", and Barendregt, Endrullis,
Klop, Waldmann (2018), "Dance of the Starlings", Fig. 5.11.

States 0..37 are accepting (strongly normalizing / halting).
State 38 (representing infinity) is rejecting (non-normalizing / non-halting).
The leaf S has state 0.
"""

from __future__ import annotations
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from s_engine import DAGPool, enumerate_trees_by_size

INF = 38

# 38 x 38 table for rows 0..37 and cols 0..37 from Fig. 5.11
RAW_ROWS = [
    "1 7 19 27 31 29 30 9 32 15 36 19 37 27 31 15 32 36 37 24 29 29 29 29 30 30 29 29 30 30 ∞ 30 26 34 35 29 25 29",
    "2 9 22 28 31 30 30 24 33 26 37 25 31 25 31 25 31 31 31 29 29 29 35 29 30 30 30 30 29 ∞ ∞ 30 30 30 ∞ ∞ 30 30",
    "3 11 24 29 29 30 30 29 29 29 29 30 29 30 30 30 30 30 30 30 29 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "4 13 25 29 29 30 30 30 29 29 29 30 29 30 30 30 30 30 30 30 29 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 14 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 5 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 6 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "8 15 26 29 29 30 30 29 34 34 35 29 29 29 29 29 29 29 29 30 29 29 29 29 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 16 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "10 15 26 29 29 30 30 29 34 35 35 29 29 29 29 29 29 29 29 30 29 29 29 29 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 17 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "12 11 25 29 29 30 30 30 29 29 29 30 29 30 30 30 30 30 30 30 29 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 18 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "4 13 25 29 29 30 30 30 29 29 29 30 29 30 30 30 30 30 30 30 29 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 14 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "10 15 26 29 29 30 30 29 34 35 35 29 29 29 29 29 29 29 29 30 29 29 29 29 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 16 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 17 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "5 18 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "20 19 25 29 29 30 30 30 29 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 21 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 21 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 23 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 23 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 24 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 25 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 26 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 27 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 28 25 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 30 30 30 ∞ ∞ ∞ ∞ ∞ 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 29 29 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 31 31 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "21 32 31 29 29 30 30 30 29 30 29 30 29 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 33 31 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 34 29 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 35 29 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "21 36 31 29 29 30 30 30 29 30 29 30 29 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
    "6 37 31 30 30 30 30 30 29 30 29 30 30 30 30 30 30 30 30 ∞ 30 30 ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞ ∞",
]


def build_table() -> tuple[tuple[int, ...], ...]:
    """Builds the 39x39 transition table DELTA[x][y] for application (M N).

    Note on Fig. 5.11 of Barendregt et al. (2018), 'Dance of the Starlings' (p. 82):
    Although the figure caption states 'row x and column y', the printed matrix actually
    places the left operand M (function, state x) on the horizontal axis (column x)
    and the right operand N (argument, state y) on the vertical axis (row y).
    Transposing the printed matrix so DELTA[x][y] = printed_row[y][x] yields 100%
    exact S-algebra conversion invariance:
        DELTA[DELTA[DELTA[0][x]][y]][z] == DELTA[DELTA[x][z]][DELTA[y][z]]
    across all 39^3 = 59,319 state triples (x, y, z).
    """
    assert len(RAW_ROWS) == 38
    raw_matrix = []
    for row_str in RAW_ROWS:
        tokens = row_str.split()
        assert len(tokens) == 38
        row = [INF if tok == "∞" else int(tok) for tok in tokens] + [INF]
        raw_matrix.append(row)
    raw_matrix.append([INF] * 39)
    # Transpose so DELTA[x][y] is column x, row y of the printed figure
    table = [
        tuple(raw_matrix[y][x] for y in range(39))
        for x in range(39)
    ]
    return tuple(table)


DELTA = build_table()


def eval_state(pool: DAGPool, node: int, cache: dict[int, int] | None = None) -> int:
    if cache is None:
        cache = {}
    if node == 0:
        return 0
    if node in cache:
        return cache[node]
    pair = pool.nodes[node]
    assert pair is not None
    s_l = eval_state(pool, pair[0], cache)
    s_r = eval_state(pool, pair[1], cache)
    res = DELTA[s_l][s_r]
    cache[node] = res
    return res


def is_normalizing(pool: DAGPool, node: int, cache: dict[int, int] | None = None) -> bool:
    return eval_state(pool, node, cache) != INF


def verify_automaton_properties() -> dict:
    # 1. Verify exact rewrite invariance: for all x, y, z in 0..38,
    #    DELTA[DELTA[DELTA[0][x]][y]][z] == DELTA[DELTA[x][z]][DELTA[y][z]]
    #    Wait: let's check both exact state equality and acceptance equivalence!
    exact_matches = 0
    accept_matches = 0
    mismatches = []
    for x in range(39):
        for y in range(39):
            for z in range(39):
                lhs = DELTA[DELTA[DELTA[0][x]][y]][z]
                rhs = DELTA[DELTA[x][z]][DELTA[y][z]]
                if lhs == rhs:
                    exact_matches += 1
                else:
                    mismatches.append((x, y, z, lhs, rhs))
                if (lhs == INF) == (rhs == INF):
                    accept_matches += 1

    # 2. Check all ground pure-S terms of size 1..10
    pool = DAGPool()
    by_size = enumerate_trees_by_size(pool, 10)
    state_cache: dict[int, int] = {0: 0}
    size_stats = {}
    for n in range(1, 11):
        halting = 0
        non_halting = 0
        for nd in by_size[n]:
            st = eval_state(pool, nd, state_cache)
            if st == INF:
                non_halting += 1
            else:
                halting += 1
        size_stats[n] = {"total": len(by_size[n]), "halting": halting, "non_halting": non_halting}

    return {
        "triples_total": 39**3,
        "exact_nerode_invariance": exact_matches,
        "acceptance_invariance": accept_matches,
        "mismatches": mismatches,
        "size_stats": size_stats,
    }


if __name__ == "__main__":
    print(json.dumps(verify_automaton_properties(), indent=2))
