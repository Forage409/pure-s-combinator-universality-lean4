"""Question II Exploration:
1. Exact Leftmost-Innermost (->_{li}) normal-form dynamical system F_li: (L_t, Z_t) in NF x NF
2. Characterization of SN state pairs (u, v) in {0..37}^2 with DELTA[u][v] == 38
3. Consecutive Case 3 step bounds across all non-halting terms of sizes 7..11, Wolfram 1..12, D_seed, Zachos
4. Rightmost-Innermost (->_{ri}) and Gross-Knuth Parallel Reduction (=>_{GK}) experiments
"""

from __future__ import annotations
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
SPRIZE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(SPRIZE))

from s_engine import DAGPool, enumerate_trees_by_size
from waldmann_automaton import DELTA as DELTA_SN, INF as INF_SN, eval_state as eval_sn
from hnf_automaton import eval_hn_state as eval_hn, INF_HN


class InnermostEngine:
    def __init__(self, pool: DAGPool):
        self.pool = pool
        self.sn_cache: dict[int, int] = {0: 0}
        self.hn_cache: dict[int, int] = {0: 0}
        self.nf_cache: dict[int, int] = {0: 0}
        self.gk_cache: dict[int, int] = {0: 0}

    def sn(self, node: int) -> int:
        return eval_sn(self.pool, node, self.sn_cache)

    def normalize_sn(self, node: int) -> int:
        """Computes exact normal form of a strongly normalizing term (unique by confluence!)."""
        assert self.sn(node) != INF_SN, f"Cannot normalize non-SN term {self.pool.to_str(node)}"
        if node in self.nf_cache:
            return self.nf_cache[node]
        sp = self.pool.spine(node)
        if len(sp) >= 3:
            # We can normalize children first or step_head; by confluence NF is identical!
            # Stepping head orGK-parallel with DAG memoization is super fast!
            nxt = self.step_gk(node)
            res = self.normalize_sn(nxt)
            self.nf_cache[node] = res
            return res
        nf_args = [self.normalize_sn(a) for a in sp]
        res = self.pool.app_many(0, nf_args)
        self.nf_cache[node] = res
        return res

    def step_gk(self, node: int) -> int:
        """One Gross-Knuth parallel reduction step (contracts ALL redexes present in node simultaneously)."""
        if node in self.gk_cache:
            return self.gk_cache[node]
        if node == 0:
            return 0
        # Check if node is a redex (((S X) Y) Z)
        p1 = self.pool.nodes[node]
        assert p1 is not None
        l1, z = p1
        if l1 != 0:
            p2 = self.pool.nodes[l1]
            assert p2 is not None
            l2, y = p2
            if l2 != 0:
                p3 = self.pool.nodes[l2]
                assert p3 is not None
                l3, x = p3
                if l3 == 0:
                    # Root is a redex S x y z! In Gross-Knuth, contract x, y, z recursively AND contract root!
                    x2 = self.step_gk(x)
                    y2 = self.step_gk(y)
                    z2 = self.step_gk(z)
                    res = self.pool.app(self.pool.app(x2, z2), self.pool.app(y2, z2))
                    self.gk_cache[node] = res
                    return res
        # Otherwise root is NOT a redex; reduce left and right children in parallel
        res = self.pool.app(self.step_gk(p1[0]), self.step_gk(p1[1]))
        self.gk_cache[node] = res
        return res

    def find_minimal_li_non_sn(self, node: int) -> tuple[int, int]:
        """Finds the leftmost-innermost subterm U* = L R with sn(U*) == 38, sn(L) < 38, sn(R) < 38,
        and returns (nf(L), nf(R))."""
        assert self.sn(node) == INF_SN
        pair = self.pool.nodes[node]
        assert pair is not None
        l, r = pair
        if self.sn(l) == INF_SN:
            return self.find_minimal_li_non_sn(l)
        if self.sn(r) == INF_SN:
            return self.find_minimal_li_non_sn(r)
        return (self.normalize_sn(l), self.normalize_sn(r))

    def step_f_li(self, L_nf: int, Z_nf: int) -> tuple[int, int, int]:
        """One macro-step of F_li on (L_nf, Z_nf) in NF x NF with DELTA[sn(L_nf)][sn(Z_nf)] == 38.
        Returns (case_num, next_L_nf, next_Z_nf) where case_num in {1, 2, 3}.
        """
        sp = self.pool.spine(L_nf)
        assert len(sp) == 2, f"Expected spine length 2 for L_nf, got {len(sp)}"
        X_nf, Y_nf = sp[0], sp[1]
        xz = self.pool.app(X_nf, Z_nf)
        if self.sn(xz) == INF_SN:
            return (1, X_nf, Z_nf)
        yz = self.pool.app(Y_nf, Z_nf)
        if self.sn(yz) == INF_SN:
            return (2, Y_nf, Z_nf)
        # Case 3: both xz and yz are SN, while (xz)(yz) is non-SN!
        L_next = self.normalize_sn(xz)
        Z_next = self.normalize_sn(yz)
        assert DELTA_SN[self.sn(L_next)][self.sn(Z_next)] == INF_SN
        return (3, L_next, Z_next)


def analyze_innermost():
    pool = DAGPool()
    eng = InnermostEngine(pool)

    # 1. Analyze all pairs (u, v) in {0..37}^2 such that DELTA_SN[u][v] == 38
    critical_pairs = []
    for u in range(38):
        for v in range(38):
            if DELTA_SN[u][v] == INF_SN:
                critical_pairs.append((u, v))

    # Which states u in {0..37} can appear as sn(S X Y) (2-argument NFs)?
    by_size = enumerate_trees_by_size(pool, 10)
    nf_states_seen: dict[int, int] = {}
    nf_2arg_states: set[int] = set()
    for sz in range(1, 11):
        for nd in by_size[sz]:
            if eng.sn(nd) != INF_SN:
                nf = eng.normalize_sn(nd)
                st = eng.sn(nf)
                nf_states_seen.setdefault(st, nf)
                if len(pool.spine(nf)) == 2:
                    nf_2arg_states.add(st)

    # Check all Case 3 state transitions: for x, y, z in {0..37} with s0xy = DELTA[DELTA[0][x]][y] < 38,
    # u = DELTA[x][z] < 38, v = DELTA[y][z] < 38, DELTA[u][v] == 38!
    case3_triples = []
    for x in range(38):
        s0x = DELTA_SN[0][x]
        if s0x == INF_SN:
            continue
        for y in range(38):
            s0xy = DELTA_SN[s0x][y]
            if s0xy == INF_SN:
                continue
            for z in range(38):
                if DELTA_SN[s0xy][z] == INF_SN:
                    u = DELTA_SN[x][z]
                    v = DELTA_SN[y][z]
                    if u != INF_SN and v != INF_SN:
                        case3_triples.append((x, y, z, s0xy, u, v))

    # Build directed graph of possible Case-3-to-Case-3 transitions on critical pairs (s0xy, z) -> (u, v)!
    # Wait: if (s0xy, z) -> (u, v) in Case 3, can (u, v) ALSO do a Case 3 step?!
    case3_pair_edges: set[tuple[tuple[int, int], tuple[int, int]]] = set()
    for x, y, z, l_st, u, v in case3_triples:
        case3_pair_edges.add(((l_st, z), (u, v)))

    # Check if case3_pair_edges has cycles or bounded DAG path length!!
    adj: dict[tuple[int, int], set[tuple[int, int]]] = {}
    nodes_c3 = set()
    for a, b in case3_pair_edges:
        adj.setdefault(a, set()).add(b)
        nodes_c3.add(a)
        nodes_c3.add(b)

    # Detect cycles in Case-3 state-pair graph!
    has_cycle_c3 = False
    cycle_examples = []
    for start in sorted(nodes_c3):
        # BFS/DFS for cycle back to start
        stack = [(start, [start])]
        visited = set()
        while stack:
            cur, path = stack.pop()
            for nxt in adj.get(cur, ()):
                if nxt == start:
                    has_cycle_c3 = True
                    if len(cycle_examples) < 5:
                        cycle_examples.append(path + [start])
                elif nxt not in visited and len(path) < 40:
                    visited.add(nxt)
                    stack.append((nxt, path + [nxt]))

    # 2. Empirically trace F_li on all non-halting terms of sizes 7..10 (1,920 terms) for 40 macro-steps!
    max_consec_case3 = 0
    max_consec_case3_term = ""
    max_consec_case3_trace = []
    case_seq_patterns = {}

    for sz in range(7, 11):
        for nd in by_size[sz]:
            if eng.sn(nd) == INF_SN:
                L, Z = eng.find_minimal_li_non_sn(nd)
                seq = []
                cur_c3 = 0
                best_c3 = 0
                for step in range(30):
                    # Guard against gigantic DAG blowup if depth > 2000
                    if pool.depth(L) > 800 or pool.depth(Z) > 800:
                        break
                    c, L, Z = eng.step_f_li(L, Z)
                    seq.append(c)
                    if c == 3:
                        cur_c3 += 1
                        best_c3 = max(best_c3, cur_c3)
                    else:
                        cur_c3 = 0
                if best_c3 > max_consec_case3:
                    max_consec_case3 = best_c3
                    max_consec_case3_term = pool.to_str(nd)
                    max_consec_case3_trace = seq
                pat = "".join(str(x) for x in seq[:16])
                case_seq_patterns[pat] = case_seq_patterns.get(pat, 0) + 1

    # Trace specific famous terms under F_li: X1, X2, D_seed, Zachos, AAA
    famous = {
        "X1_S(SS)SSSS": "S(SS)SSSS",
        "X2_SSS(SS)SS": "SSS(SS)SS",
        "AAA": "(SSS)(SSS)(SSS)",
        "Zachos_9": "SSS(S(SS))(SS)",
        "D_seed": "S(S(SS))(S(SS))(SS)S",
    }
    famous_traces = {}
    for name, expr in famous.items():
        nd = pool.parse(expr)
        L, Z = eng.find_minimal_li_non_sn(nd)
        trace = []
        for step in range(25):
            if pool.depth(L) > 1000 or pool.depth(Z) > 1000:
                break
            st_pair = (eng.sn(L), eng.sn(Z))
            d_pair = (pool.depth(L), pool.depth(Z))
            c, L, Z = eng.step_f_li(L, Z)
            trace.append({"step": step, "case": c, "state_pair": st_pair, "depths": d_pair})
        famous_traces[name] = trace

    return {
        "critical_pairs_count": len(critical_pairs),
        "nf_states_seen_count": len(nf_states_seen),
        "nf_2arg_states": sorted(nf_2arg_states),
        "case3_triples_count": len(case3_triples),
        "case3_pair_edges_count": len(case3_pair_edges),
        "case3_state_graph_has_cycle": has_cycle_c3,
        "case3_cycle_examples": cycle_examples,
        "max_consec_case3_observed_sizes_7_10": max_consec_case3,
        "max_consec_case3_witness": max_consec_case3_term,
        "max_consec_case3_trace": max_consec_case3_trace,
        "top_case_seq_patterns": sorted(case_seq_patterns.items(), key=lambda kv: -kv[1])[:20],
        "famous_traces": famous_traces,
    }


if __name__ == "__main__":
    res = analyze_innermost()
    out_path = Path(__file__).parent / "q2_innermost_results.json"
    out_path.write_text(json.dumps(res, indent=2), encoding="utf-8")
    print("Saved q2_innermost_results.json")
    print("Critical pairs count:", res["critical_pairs_count"])
    print("Case 3 triples:", res["case3_triples_count"], "Pair edges:", res["case3_pair_edges_count"])
    print("Case 3 state graph has cycle?", res["case3_state_graph_has_cycle"], "Examples:", res["case3_cycle_examples"][:2])
    print("Max consecutive Case 3 observed (sizes 7..10):", res["max_consec_case3_observed_sizes_7_10"], "on", res["max_consec_case3_witness"])
    print("Top F_li case patterns:", res["top_case_seq_patterns"][:10])
    for k, tr in res["famous_traces"].items():
        print(f"  {k}: cases={[t['case'] for t in tr[:18]]}")
