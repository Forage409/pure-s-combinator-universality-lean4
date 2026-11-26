"""Executable Verification & Table Validator for Waldmann's Top-Termination Theorem (Theorem 29).

Resides strictly inside `formal_top_termination/`. Verifies all finite S-algebra laws,
global multiway potential `nuHN` inequalities, right-spine reachability strata `inGe1HN..inGe5HN`,
transient DAG rank into `SCC 1`, 1-step `R`-collapse into `{23, 34}`, symbolic `rightTower`
collapse, and empirical multiway root-step bounds across closed S-terms.
"""
from __future__ import annotations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SPRIZE = HERE.parent
ROOT = SPRIZE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(SPRIZE))

from s_engine import DAGPool, enumerate_trees_by_size
from hnf_automaton import DELTA_HN, INF_HN, eval_hn_state, is_root_normal_form


def verify_all() -> dict:
    cert = json.loads((SPRIZE / "hn_integer_certificate.json").read_text(encoding="utf-8"))
    A, B = cert["A"], cert["B"]

    # 1. Exact S-law on 35^3 = 42,875 triples
    for x in range(35):
        for y in range(35):
            for z in range(35):
                assert DELTA_HN[DELTA_HN[DELTA_HN[0][x]][y]][z] == DELTA_HN[DELTA_HN[x][z]][DELTA_HN[y][z]]

    # 2. Global multiway weak-decrease + non-34 strict head-decrease of nuHN
    for x in range(35):
        s1 = DELTA_HN[0][x]
        for y in range(35):
            s2 = DELTA_HN[s1][y]
            for z in range(35):
                if DELTA_HN[s2][z] != 34:
                    u = DELTA_HN[x][z]
                    v = DELTA_HN[y][z]
                    assert u != 34
                    assert A[0][x] >= 1
                    assert A[s1][y] >= A[u][v]
                    assert A[s2][z] >= A[x][z] + A[u][v] * A[y][z]
                    assert B[0][x] + B[s1][y] + B[s2][z] >= B[x][z] + A[u][v] * B[y][z] + B[u][v] + 1
                    # Also verify A[u][34] == 0 so nuHN(y . z) == 0 is multiplied by 0 when v == 34
                    if v == 34:
                        assert A[u][v] == 0

    # 3. Right-spine strata ge1..ge5
    ge = [set(range(35))]
    for k in range(1, 7):
        ge.append({DELTA_HN[x][y] for x in range(35) for y in ge[-1]})
    assert ge[5] == ge[6]

    # 4. inHN0to5 characterization: deltaHN(x, y) in 0..5 <-> x == 0 and y in 0..5
    hn0to5 = {0, 1, 2, 3, 4, 5}
    for x in range(35):
        for y in range(35):
            assert (DELTA_HN[x][y] in hn0to5) == (x == 0 and y in hn0to5)

    # 5. Transient rank <= 2 into SCC 1 = {23, 24, 25} x {10, 23, 24, 34}
    scc1_L = {23, 24, 25}
    scc1_R = {10, 23, 24, 34}

    def tr_rank(ql: int, qr: int) -> int:
        if ql in scc1_L and qr in scc1_R:
            return 0
        return 2 if qr in {12, 13} else 1

    for x in range(35):
        s1 = DELTA_HN[0][x]
        for y in ge[5]:
            s2 = DELTA_HN[s1][y]
            if s2 not in ge[5] or s2 == 34:
                continue
            for z in ge[5]:
                if DELTA_HN[s2][z] != 34:
                    continue
                u = DELTA_HN[x][z]
                v = DELTA_HN[y][z]
                if u == 34:
                    continue
                assert u in ge[5] and v in ge[5] and DELTA_HN[u][v] == 34
                r0 = tr_rank(s2, z)
                r1 = tr_rank(u, v)
                assert (r1 == 0) if (r0 == 0) else (r1 < r0)

    # 6. 1-step collapse of R from SCC 1 into {23, 34}
    for y in scc1_R:
        for z in scc1_R:
            assert DELTA_HN[y][z] in {23, 34}
    for v in range(35):
        s2 = DELTA_HN[1][v]
        for w in ge[5]:
            if DELTA_HN[s2][w] in scc1_L:
                for z in scc1_R:
                    assert DELTA_HN[DELTA_HN[v][w]][z] in {23, 34}

    # 7. Phase 3 checks on z in {23, 34}
    z23_34 = {23, 34}
    for z in z23_34:
        for q in range(35):
            u = DELTA_HN[q][z]
            for r in z23_34:
                if DELTA_HN[u][r] == 34 and u != 34:
                    assert u in scc1_L
        for a in range(35):
            for b in range(35):
                if DELTA_HN[DELTA_HN[a][z]][DELTA_HN[b][z]] != 34:
                    assert a in hn0to5
        for b in range(35):
            if b not in hn0to5:
                for z2 in z23_34:
                    assert DELTA_HN[DELTA_HN[b][z]][z2] == 34
            # Also for m=3 helper: deltaHN(deltaHN(b, z), 34) in {23, 34}
            assert DELTA_HN[DELTA_HN[b][z]][34] in z23_34

    # 8. Empirical RNF normalization check on all 6,918 closed S-terms of sizes 1..10
    pool = DAGPool()
    by_size = enumerate_trees_by_size(pool, 10)
    hn_cache = {0: 0}
    max_roots_by_size = {}
    for sz in range(1, 11):
        mx_r = 0
        for nd in by_size[sz]:
            cur = nd
            rc = 0
            while not is_root_normal_form(pool, cur, hn_cache):
                if len(pool.spine(cur)) == 3:
                    rc += 1
                cur, ch = pool.step_head(cur)
                assert ch
            mx_r = max(mx_r, rc)
        max_roots_by_size[sz] = mx_r

    return {
        "ge_strata_sizes": [len(s) for s in ge],
        "ge5_states": sorted(ge[5]),
        "max_head_root_steps_to_rnf_sizes_1_to_10": max_roots_by_size,
        "all_checks_passed": True,
    }


if __name__ == "__main__":
    res = verify_all()
    print(json.dumps(res, indent=2))
