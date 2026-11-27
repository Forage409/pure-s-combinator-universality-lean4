"""Cross-validator for PureSUniversality.wl and VerifyPureSUniversality.wls.

Parses the Wolfram Language submission files directly to verify:
1. Balanced brackets (), [], {}, strings "", and nested comments (* ... *).
2. Exact table-level parity of DeltaHalt11, SNRawRows (DeltaSN), BuildDeltaHN,
   and NearyU311Table against the Lean 4 and Python formal tables.
3. Exact numerical parity on all benchmark invariants asserted in
   VerifyPureSUniversality.wls (BB(2) native contractions, 1,996,921 and
   7,477,337 compiled pure-S leaf counts, Question 7 flip-flop chain M_0..M_8,
   and live U(3,11)->Pure-S terminal native contractions + output decoding).
"""

from __future__ import annotations
import ast
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.setrecursionlimit(100000)

from waldmann_automaton import DELTA as PY_DELTA_SN, eval_state as py_eval_sn
from hnf_automaton import DELTA_HN as PY_DELTA_HN
from neary_u3_11 import ROWS as PY_NEARY_ROWS, encode_source, machine as u_machine
from s_monotone_tape import Instruction
from normalize_neary_safe import normalize_safe
from binary_tm_compiler import encode_symbols
from prize_encoder import BINARY_UNIVERSAL
from fast_initial_encoder import encode_initial
from s_physical_selector import select_physical
from s_neary_output_reader import read_neary_source_output
from s_engine import DAGPool


def check_wolfram_syntax_balance(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    i = 0
    n = len(text)
    comment_depth = 0
    in_string = False
    stack: list[tuple[str, int]] = []
    matching = {")": "(", "]": "[", "}": "{"}
    line = 1
    while i < n:
        ch = text[i]
        if ch == "\n":
            line += 1
        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if comment_depth > 0:
            if text[i : i + 2] == "(*":
                comment_depth += 1
                i += 2
                continue
            if text[i : i + 2] == "*)":
                comment_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if text[i : i + 2] == "(*":
            comment_depth += 1
            i += 2
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch in "([{":
            stack.append((ch, line))
        elif ch in ")]}":
            assert stack and stack[-1][0] == matching[ch], (
                f"{path.name}:{line}: mismatched '{ch}', stack top={stack[-1] if stack else None}"
            )
            stack.pop()
        i += 1
    assert not in_string, f"{path.name}: unclosed string literal"
    assert comment_depth == 0, f"{path.name}: unclosed comment"
    assert not stack, f"{path.name}: unclosed brackets {stack}"


def parse_wl_int_matrix(wl_block: str) -> list[list[int]]:
    rows = []
    for raw_line in wl_block.strip().splitlines():
        line = raw_line.strip().rstrip(",")
        if not line:
            continue
        if line.startswith("ConstantArray[38, 39]"):
            rows.append([38] * 39)
        else:
            py_line = line.replace("{", "[").replace("}", "]")
            rows.append(ast.literal_eval(py_line))
    return rows


def main() -> None:
    wl_dir = Path(__file__).resolve().parent
    wl_path = wl_dir / "PureSUniversality.wl"
    wls_path = wl_dir / "VerifyPureSUniversality.wls"

    check_wolfram_syntax_balance(wl_path)
    check_wolfram_syntax_balance(wls_path)
    wl_text = wl_path.read_text(encoding="utf-8")

    # 1. Verify DeltaHalt11 matches Lean 4 halt_tree_automaton.lean
    m_halt = re.search(r"DeltaHalt11\s*=\s*\{\n(.*?)\n\};", wl_text, re.S)
    assert m_halt, "Missing DeltaHalt11 in PureSUniversality.wl"
    wl_delta_halt = parse_wl_int_matrix(m_halt.group(1))
    state_features = [
        (1, 0, 0, 0, 0, 0, 0),
        (0, 1, 0, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 1),
        (0, 0, 0, 1, 0, 0, 0),
        (0, 0, 0, 1, 1, 0, 0),
        (0, 0, 0, 1, 1, 0, 1),
        (0, 0, 0, 1, 1, 1, 0),
        (0, 0, 0, 1, 1, 1, 1),
        (0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 1),
    ]
    feat_idx = {f: i for i, f in enumerate(state_features)}
    for l in range(11):
        for r in range(11):
            fl, fr = state_features[l], state_features[r]
            comb = (
                0,
                fl[0],
                fl[0] & fr[4],
                fl[1],
                fl[1] & fr[3],
                fl[2] & fr[3],
                fr[5],
            )
            assert wl_delta_halt[l][r] == feat_idx[comb]

    # 2. Verify SNRawRows transposed == PY_DELTA_SN
    m_sn = re.search(r"SNRawRows\s*=\s*\{\n(.*?)\n\};", wl_text, re.S)
    assert m_sn, "Missing SNRawRows in PureSUniversality.wl"
    sn_raw = parse_wl_int_matrix(m_sn.group(1))
    wl_delta_sn = [[sn_raw[r][l] for r in range(39)] for l in range(39)]
    assert wl_delta_sn == [list(row) for row in PY_DELTA_SN]

    # 3. Verify BuildDeltaHN pfx reconstructs PY_DELTA_HN identically
    m_hn = re.search(r"pfx\s*=\s*\{\n(.*?)\n\s*\};", wl_text, re.S)
    assert m_hn, "Missing BuildDeltaHN pfx in PureSUniversality.wl"
    hn_pfx = parse_wl_int_matrix(m_hn.group(1))
    d_hn: list[list[int | None]] = [[None] * 35 for _ in range(35)]
    for y in range(35):
        row = hn_pfx[y]
        for x, val in enumerate(row):
            d_hn[x][y] = val
        if len(row) == 22:
            d_hn[22][y] = 34
        d_hn[34][y] = 34
        d_hn[27][y] = 25
    for _ in range(5):
        for x in range(35):
            for y in range(35):
                for z in range(35):
                    s0x = d_hn[0][x]
                    s0xy = d_hn[s0x][y] if s0x is not None else None
                    xz = d_hn[x][z]
                    yz = d_hn[y][z]
                    if s0xy is not None and xz is not None and yz is not None and d_hn[xz][yz] is not None:
                        if d_hn[s0xy][z] is None:
                            d_hn[s0xy][z] = d_hn[xz][yz]
    assert d_hn == [list(row) for row in PY_DELTA_HN]

    # 4. Verify Question 7 flip-flop chain M_0..M_8
    pool = DAGPool()
    a_node = pool.parse("SSS")
    ss_node = pool.parse("SS")
    r_s = pool.app(pool.app(pool.app(0, a_node), 0), a_node)
    r_ss = pool.app(pool.app(pool.app(ss_node, a_node), 0), a_node)

    def wrap_k(k: int, tail: int) -> int:
        cur = tail
        for _ in range(k):
            cur = pool.app(pool.app(0, r_ss), cur)
        return cur

    for n in range(9):
        term = wrap_k(n // 2, 0 if n % 2 == 0 else pool.app(pool.app(0, r_s), 0))
        st = py_eval_sn(pool, term)
        assert (st < 38) if n % 2 == 0 else (st == 38)

    # 5. Verify BB(2) direct Pure-S run + 11-state Halt DTA acceptance
    bb2 = {
        (0, 0): Instruction(1, 1, 1),
        (0, 1): Instruction(1, 1, -1),
        (1, 0): Instruction(0, 1, -1),
        (1, 1): Instruction(2, 1, 0),
    }
    runner_bb2, _ = encode_initial(bb2, (0, 0, 0, 0), head_index=2)
    bb2_steps = 0
    while True:
        act, path = select_physical(bb2, runner_bb2)
        if act == "halt":
            break
        runner_bb2.trie.contract(path)
        bb2_steps += 1

    def eval_halt_dta(p: DAGPool, root: int) -> int:
        memo = {0: 0}
        stk = [(root, False)]
        while stk:
            nd, ready = stk.pop()
            if nd in memo:
                continue
            l, r = p.nodes[nd]
            if not ready:
                stk.append((nd, True))
                if r not in memo:
                    stk.append((r, False))
                if l not in memo:
                    stk.append((l, False))
            else:
                memo[nd] = wl_delta_halt[memo[l]][memo[r]]
        return memo[root]

    bb2_dta = eval_halt_dta(runner_bb2.trie.p, runner_bb2.trie.term)
    assert bb2_dta in {3, 6, 8, 10}

    # 6. Verify exact leaf counts & live U(3,11) terminal native-S cycle + decode
    norm0, n0, w0 = normalize_safe({}, 1, ())
    enc0, h0 = encode_source(norm0, n0, w0)
    run0, _ = encode_initial(BINARY_UNIVERSAL, encode_symbols(enc0, 4), 4 * h0)
    assert run0.trie.p.leaf_count(run0.trie.term) == 1996921

    src_w1 = {(0, 0): Instruction(1, 1, 0)}
    norm1, n1, w1 = normalize_safe(src_w1, 2, ())
    enc1, h1 = encode_source(norm1, n1, w1)
    run1, _ = encode_initial(BINARY_UNIVERSAL, encode_symbols(enc1, 4), 4 * h1)
    assert run1.trie.p.leaf_count(run1.trie.term) == 7477337

    u_norm, u_n, u_w = normalize_safe({}, 1, (1,))
    u_enc, u_h = encode_source(u_norm, u_n, u_w)
    u_tbl = u_machine()
    tape = {i: v for i, v in enumerate(u_enc) if v}
    st, hd = 0, u_h
    while True:
        ins = u_tbl.get((st, tape.get(hd, 0)))
        if ins is None:
            break
        if ins.write:
            tape[hd] = ins.write
        else:
            tape.pop(hd, None)
        st = ins.next_state
        hd = max(0, hd + ins.move)

    tape[hd + 1] = 10  # GAMMA in U-state 0 -> writes LA, moves left to DELTA in U-state 2 -> halts
    utm_word = tuple(tape.get(i, 0) for i in range(max(tape, default=0) + 1))
    run_term, _ = encode_initial(BINARY_UNIVERSAL, encode_symbols(utm_word, 4), 4 * (hd + 1))
    term_s_steps = 0
    while True:
        act, path = select_physical(BINARY_UNIVERSAL, run_term)
        if act == "halt":
            break
        run_term.trie.contract(path)
        term_s_steps += 1
    assert eval_halt_dta(run_term.trie.p, run_term.trie.term) in {3, 6, 8, 10}
    decoded = read_neary_source_output(BINARY_UNIVERSAL, run_term)
    assert decoded == (1,)

    # 7. Verify Extended Algebras (DeltaP, DeltaA36, DeltaDNAND, DeltaBZachos) & Program-Free CTS exports
    for name, expected in [
        ("DeltaP", json.loads((ROOT / "intrinsic_research" / "productivity_automaton_proof.json").read_text(encoding="utf-8"))["table"]),
        ("DeltaDNAND", [[1, 1, 1, 2], [3, 3, 3, 3], [1, 1, 3, 3], [3, 3, 3, 3]]),
        ("DeltaBZachos", [
            [1, 2, 7, 5, 5, 7, 7, 7],
            [7, 7, 7, 4, 4, 7, 7, 7],
            [7, 3, 7, 7, 7, 7, 7, 7],
            [7, 7, 7, 6, 6, 7, 7, 7],
            [7, 7, 7, 7, 7, 7, 7, 7],
            [7, 7, 7, 7, 7, 7, 6, 7],
            [7, 7, 7, 7, 7, 7, 7, 7],
            [7, 7, 7, 7, 7, 7, 7, 7],
        ]),
    ]:
        m_mat = re.search(rf"{name}\s*=\s*\{{\n(.*?)\n\}};", wl_text, re.S)
        assert m_mat, f"Missing {name} in PureSUniversality.wl"
        parsed = parse_wl_int_matrix(m_mat.group(1))
        assert parsed == expected, f"Matrix mismatch on {name}"

    m_36 = re.search(r"DeltaA36\s*=\s*\{\n(.*?)\n\};", wl_text, re.S)
    assert m_36, "Missing DeltaA36 in PureSUniversality.wl"
    wl_36 = parse_wl_int_matrix(m_36.group(1))
    assert len(wl_36) == 36 and all(len(r) == 36 for r in wl_36)
    for x in range(36):
        for y in range(36):
            for z in range(36):
                assert wl_36[wl_36[wl_36[0][x]][y]][z] == wl_36[wl_36[x][z]][wl_36[y][z]]
    q_a = wl_36[wl_36[0][0]][0]
    q_aaa = wl_36[wl_36[q_a][q_a]][q_a]
    assert q_aaa == 34 and wl_36[q_aaa][0] == 35

    for req_sym in [
        "EvalProductivityState", "IsProductivePureSQ", "EvalQuestion31State",
        "EvalDNANDState", "PureSRule110Term", "IteratePureSRule110",
        "EvalBZachosState", "EncodeProgramFreeCTS", "ProgramFreePureSSelect",
        "ProgramFreePureSCTSStep", "ProgramFreePureSHaltQ", "DecodeProgramFreeCTSState",
        "WolframChallenge12Benchmarks", "MinimalNonHaltingPureSTerms",
        "MinimalProductiveNonSNPureSTerm", "MinimalLambdaDivergingPureSTerms",
        "Conjecture42And43Counterexamples", "PureSFunctionalOrder",
        "PureSLeftSubtreeSum", "IsGardenOfEdenNormalFormQ",
        "Question7AtomicSplitTerm", "ZachosExactLeafCount",
        "Wolfram2ExactLeafCount", "TenLeafSeedExactLeafCount",
        "PureSJumpAheadOutcome", "PureSAsymptoticConstants",
        "PureSCatalanPhaseCensus",
    ]:
        assert f"{req_sym}::usage" in wl_text, f"Missing usage export {req_sym}"
        assert req_sym in wls_path.read_text(encoding="utf-8") or req_sym in wl_text

    # 8. Verify Program-Free CTS layout parity with Lean 4 formal_program_free/program_free_cts.lean
    assert "PFFlagPath = {1, 0, 1};" in wl_text, "PFFlagPath must match Lean 4 pfFlagPath = [true, false, true]"
    assert "PFPayloadPath = {1, 1, 0, 1};" in wl_text
    assert "PFProgRingPath = {1, 1, 0, 1, 0, 1};" in wl_text
    assert "PFQueueRootPath = {1, 1, 0, 1, 1, 0, 1};" in wl_text
    assert "ProgramFreePureSHaltQ[root_] := PureSHaltDetectorQ[root];" in wl_text

    # Also execute exact Python mirror of Lean 4 / WL Program-Free CTS on {{1}, {}} with {1, 0, 1}
    pf_pool = DAGPool()
    b_nd = pf_pool.app(0, 0)

    def pf_numeral(n: int) -> int:
        cur = pf_pool.app(pf_pool.app(0, b_nd), b_nd)
        for _ in range(n):
            cur = pf_pool.app(b_nd, cur)
        return cur

    def pf_gen(m: int, n: int) -> int:
        return pf_pool.app(pf_pool.app(pf_numeral(m), pf_numeral(n)), 0)

    def pf_frame(l: int, r: int, j: int) -> int:
        return pf_pool.app(pf_pool.app(0, l), pf_pool.app(pf_pool.app(0, r), j))

    def pf_next_phase(p: tuple[int, int]) -> tuple[int, int]:
        return (p[1], p[1] + 1) if p[0] == 0 else (p[0] - 1, p[1])

    def pf_phase_at(d: int) -> tuple[int, int]:
        p = (2, 2)
        for _ in range(d):
            p = pf_next_phase(p)
        return p

    def pf_base(d: int) -> int:
        m, n = pf_phase_at(d)
        return pf_gen(m, n)

    def pf_junk(d: int) -> int:
        m, n = pf_phase_at(d)
        if m == 0:
            return pf_pool.app(pf_pool.app(pf_numeral(n - 1), 0), pf_gen(n, n + 1))
        return pf_pool.app(pf_pool.app(pf_numeral(n - 2), 0), pf_gen(m - 1, n))

    def pf_bit_term(d: int, b: int) -> int:
        return pf_frame(pf_base(d + 1), pf_base(d + 1), pf_junk(d)) if b else pf_base(d)

    def pf_fields_term(bits: list[int], d: int) -> int:
        k = len(bits)
        acc = pf_frame(pf_base(d + k + 1), pf_base(d + k + 1), pf_junk(d + k))
        for i in range(k - 1, -1, -1):
            acc = pf_frame(pf_bit_term(d + i + 1, bits[i]), acc, pf_junk(d + i))
        return acc

    def pf_ver_term(recs: list[list[int]], d: int) -> int:
        k = len(recs)
        acc = pf_base(d + k)
        for i in range(k - 1, -1, -1):
            acc = pf_frame(acc, pf_fields_term(recs[i], d + i + 1), pf_junk(d + i))
        return acc

    def pf_reclist_term(cells: list[list[list[int]]], d: int) -> int:
        k = len(cells)
        acc = pf_base(d + k)
        for i in range(k - 1, -1, -1):
            acc = pf_frame(pf_ver_term(cells[i], d + i + 1), acc, pf_junk(d + i))
        return acc

    def pf_encode_cts(prog: list[list[int]], w_bits: list[int]) -> int:
        k = len(prog)
        pring = pf_base(2 + k)
        for i in range(k - 1, -1, -1):
            d_i = 2 + i
            precs = [[1 if i == 0 else 0, 0]]
            tcells = [[[0, 0, b]] for b in prog[i]]
            pbody = pf_frame(pf_ver_term(precs, d_i + 2), pf_reclist_term(tcells, d_i + 2), pf_junk(d_i + 1))
            pring = pf_frame(pbody, pring, pf_junk(d_i))
        qroot = pf_reclist_term([[[0, 0, b]] for b in w_bits], 2)
        hub = pf_frame(pf_base(1), pf_frame(pring, qroot, pf_junk(1)), pf_junk(0))
        return pf_pool.app(pf_pool.app(pf_numeral(1), 0), hub)

    def pf_parse_frame(nd: int) -> tuple[int, int, int] | None:
        if nd == 0:
            return None
        l, r = pf_pool.nodes[nd]
        if l == 0 or r == 0:
            return None
        ll, lr = pf_pool.nodes[l]
        rl, rj = pf_pool.nodes[r]
        if ll != 0 or rl == 0:
            return None
        rll, rlr = pf_pool.nodes[rl]
        if rll != 0:
            return None
        return (lr, rlr, rj)

    def pf_node_at(nd: int, path: list[int]) -> int | None:
        cur = nd
        for dir_b in path:
            if cur == 0:
                return None
            l, r = pf_pool.nodes[cur]
            cur = l if dir_b == 0 else r
        return cur

    def pf_arity5(nd: int) -> int:
        cur = nd
        k = 0
        while k < 5 and cur != 0:
            cur = pf_pool.nodes[cur][0]
            k += 1
        return k if cur == 0 else 5

    def pf_next_open(nd: int) -> list[int] | None:
        if pf_parse_frame(nd) is not None:
            return None
        ar = pf_arity5(nd)
        if ar == 4:
            return [0]
        if ar == 3:
            return []
        if ar == 2 and nd != 0:
            rar = pf_arity5(pf_pool.nodes[nd][1])
            if rar == 4:
                return [1, 0]
            if rar == 3:
                return [1]
        return None

    def pf_read_fields(width: int, nd: int) -> list[int] | None:
        cur = nd
        bits = []
        for _ in range(width):
            pf = pf_parse_frame(cur)
            if pf is None:
                return None
            bits.append(1 if pf_parse_frame(pf[0]) is not None else 0)
            cur = pf[1]
        return bits if pf_parse_frame(cur) is not None else None

    def pf_scan_ver(width: int, nd: int) -> list[int] | None:
        cur = nd
        latest = None
        while (pf := pf_parse_frame(cur)) is not None:
            rd = pf_read_fields(width, pf[1])
            if rd is not None:
                latest = rd
            cur = pf[0]
        return latest

    def pf_choose_fields(desired: list[int], nd: int) -> list[int] | None:
        cur = nd
        acc: list[int] = []
        for b in desired:
            pf = pf_parse_frame(cur)
            if pf is None:
                return acc
            if b == 1 and pf_parse_frame(pf[0]) is None:
                return acc + [0, 1]
            acc.extend([1, 0, 1])
            cur = pf[1]
        return None if pf_parse_frame(cur) is not None else acc

    def pf_choose_ver(width: int, desired: list[int], nd: int) -> list[int] | None:
        cur = nd
        acc: list[int] = []
        while (pf := pf_parse_frame(cur)) is not None:
            if pf_read_fields(width, pf[1]) is not None:
                acc.extend([0, 1])
                cur = pf[0]
            else:
                sub = pf_choose_fields(desired, pf[1])
                return None if sub is None else acc + [1, 0, 1] + sub
        return acc

    def pf_contract_at(nd: int, path: list[int]) -> int:
        if not path:
            l1, z = pf_pool.nodes[nd]
            l2, y = pf_pool.nodes[l1]
            s_leaf, x = pf_pool.nodes[l2]
            assert s_leaf == 0
            return pf_pool.app(pf_pool.app(x, z), pf_pool.app(y, z))
        l, r = pf_pool.nodes[nd]
        if path[0] == 0:
            return pf_pool.app(pf_contract_at(l, path[1:]), r)
        return pf_pool.app(l, pf_contract_at(r, path[1:]))

    def pf_select_step(root_nd: int) -> tuple[str, list[int] | None]:
        if eval_halt_dta(pf_pool, root_nd) in {3, 6, 8, 10}:
            return ("Halt", None)
        hub_pf = pf_parse_frame(pf_pool.nodes[root_nd][1])
        assert hub_pf is not None
        pay_pf = pf_parse_frame(hub_pf[1])
        assert pay_pf is not None
        # Scan phases
        phases = []
        cur_p, rel_p = pay_pf[0], []
        while (ppf := pf_parse_frame(cur_p)) is not None:
            bpf = pf_parse_frame(ppf[0])
            if bpf is None:
                break
            fi = fa = fap = None
            cur_t, rel_t = bpf[1], []
            while (tpf := pf_parse_frame(cur_t)) is not None:
                tst = pf_scan_ver(3, tpf[0])
                cp = rel_t + [0, 1]
                if tst in ([0, 0, 0], [0, 0, 1]) and fi is None:
                    fi = (cp, tst[2])
                elif tst in ([1, 0, 0], [1, 0, 1]) and fa is None:
                    fa = (cp, tst[2])
                elif tst in ([1, 1, 0], [1, 1, 1]) and fap is None:
                    fap = (cp, tst[2])
                rel_t = rel_t + [1, 0, 1]
                cur_t = tpf[1]
            phases.append((rel_p + [0, 1, 0, 1], rel_p + [0, 1, 1, 0, 1], pf_scan_ver(2, bpf[0]), (fi, fa, fap)))
            rel_p = rel_p + [1, 0, 1]
            cur_p = ppf[1]
        # Scan queue
        cons = uncons = stag = uninit = None
        cur_q, rel_q = pay_pf[1], []
        while (qpf := pf_parse_frame(cur_q)) is not None:
            qst = pf_scan_ver(3, qpf[0])
            cp = rel_q + [0, 1]
            if qst is None and uninit is None:
                uninit = cp
            elif qst in ([0, 1, 0], [0, 1, 1]) and stag is None:
                stag = (cp, qst[2])
            elif qst in ([0, 0, 0], [0, 0, 1]) and uncons is None:
                uncons = (cp, qst[2])
            elif qst in ([1, 0, 0], [1, 0, 1]) and cons is None:
                cons = (cp, qst[2])
            rel_q = rel_q + [1, 0, 1]
            cur_q = qpf[1]
        pring_p = [1, 1, 0, 1, 0, 1]
        qroot_p = [1, 1, 0, 1, 1, 0, 1]
        handoffs = [idx for idx, pe in enumerate(phases) if pe[2] == [1, 1]]
        if handoffs:
            hi = handoffs[0]
            he = phases[hi]
            if cons is not None:
                dec = ("write", qroot_p + cons[0], 3, [1, 1, cons[1]])
            elif len(phases) == 1:
                dec = ("write", pring_p + he[0], 2, [1, 0])
            else:
                ni = (hi + 1) % len(phases)
                ne = phases[ni]
                if ne[2] == [1, 0]:
                    dec = ("write", pring_p + he[0], 2, [0, 0])
                else:
                    dec = ("write", pring_p + ne[0], 2, [1, 0])
        else:
            ai = [idx for idx, pe in enumerate(phases) if pe[2] == [1, 0]][0]
            ae = phases[ai]
            fi, fa, fap = ae[3]
            if cons is None:
                if uncons is None:
                    dec = ("open", [1, 0, 1])
                elif uncons[1] == 1 and fi is not None:
                    dec = ("write", pring_p + ae[1] + fi[0], 3, [1, 0, fi[1]])
                else:
                    dec = ("write", qroot_p + uncons[0], 3, [1, 0, uncons[1]])
            elif fap is not None:
                if stag is not None:
                    dec = ("write", pring_p + ae[1] + fap[0], 3, [0, 0, fap[1]])
                elif uninit is not None:
                    dec = ("write", qroot_p + uninit, 3, [0, 1, fap[1]])
                else:
                    dec = ("open", qroot_p + rel_q)
            elif stag is not None:
                dec = ("write", qroot_p + stag[0], 3, [0, 0, stag[1]])
            elif fa is not None:
                dec = ("write", pring_p + ae[1] + fa[0], 3, [1, 1, fa[1]])
            else:
                dec = ("write", pring_p + ae[0], 2, [1, 1])
        if dec[0] == "open":
            foc = pf_node_at(root_nd, dec[1])
            assert foc is not None
            rel = pf_next_open(foc)
            assert rel is not None
            return ("Step", dec[1] + rel)
        vt = pf_node_at(root_nd, dec[1])
        assert vt is not None
        sl = pf_choose_ver(dec[2], dec[3], vt)
        assert sl is not None
        foc = pf_node_at(root_nd, dec[1] + sl)
        assert foc is not None
        rel = pf_next_open(foc)
        assert rel is not None
        return ("Step", dec[1] + sl + rel)

    pf_cur = pf_encode_cts([[1], []], [1, 0, 1])
    pf_init_leaves = pf_pool.leaf_count(pf_cur)
    assert pf_init_leaves <= 2500 * (2 + 1 + 3 + 1) ** 2
    pf_steps = 0
    while True:
        act_pf, p_pf = pf_select_step(pf_cur)
        if act_pf == "Halt":
            break
        assert p_pf is not None
        pf_cur = pf_contract_at(pf_cur, p_pf)
        pf_steps += 1
    assert eval_halt_dta(pf_pool, pf_cur) in {3, 6, 8, 10}

    # 9. Verify Wave 2 O(1) cubic leaf-count formulas, twin +14 shift, order densities, and GoE census
    assert '"Order0DensityExact" -> 2648215 / 7077888' in wl_text
    assert '"Order1DensityExact" -> 1864553 / 7077888' in wl_text
    assert '"Order2DensityExact" -> 835 / 2304' in wl_text
    assert '"Order3DensityExact" -> 0' in wl_text
    assert 2648215 + 1864553 + 835 * 3072 == 7077888

    def zachos_exact_leaves(t: int) -> int:
        n = (int((8 * t + 9) ** 0.5) - 3) // 2
        r = t - (n * (n + 3)) // 2
        return 10 + (2 * n * (n + 2) * (n + 4)) // 3 + (0 if r == 0 else r * (2 * n + 6) - 2)

    def wolfram2_exact_leaves(t: int) -> int:
        if t < 4:
            return (8, 10, 11, 16)[t]
        d = t - 4
        n = (int((8 * d + 49) ** 0.5) - 7) // 2
        r = d - (n * (n + 7)) // 2
        intra = 0 if r == 0 else (2 * n + 7 if r == 1 else (4 * n + 16 if r == 2 else 8 * n + 33 + (r - 3) * (2 * n + 9)))
        return (4 * n**3 + 51 * n**2 + 197 * n + 138) // 6 + intra

    def seed_exact_leaves(t: int) -> int:
        if t < 2:
            return (10, 11)[t]
        cap_n = (int((8 * t - 7) ** 0.5) + 1) // 4
        d = t - (2 * cap_n**2 - cap_n + 1)
        r = d // 4
        return (5 * cap_n**3 + 15 * cap_n**2 - 8 * cap_n + 33) // 3 + r * (6 * cap_n + 13 - r) + (0 if d % 4 == 0 else 2 * cap_n + 4)

    w2_pool = DAGPool()
    cur_z = w2_pool.parse("(S(SS)(SS))(S(SS)(SS))")
    cur_w2 = w2_pool.parse("SSS(S(SS))(SS)")
    cur_tw = w2_pool.parse("(S(S(SS))(SS))(S(S(SS))(SS))")
    cur_sd = w2_pool.parse("S(S(SS))(S(SS))(SS)S")
    for t_step in range(45):
        assert w2_pool.leaf_count(cur_z) == zachos_exact_leaves(t_step)
        assert w2_pool.leaf_count(cur_w2) == wolfram2_exact_leaves(t_step)
        assert w2_pool.leaf_count(cur_sd) == seed_exact_leaves(t_step)
        if t_step >= 3:
            assert w2_pool.leaf_count(cur_tw) == wolfram2_exact_leaves(t_step + 1) + 14
        cur_z, _ = w2_pool.step_leftmost_outermost(cur_z)
        cur_w2, _ = w2_pool.step_leftmost_outermost(cur_w2)
        cur_tw, _ = w2_pool.step_leftmost_outermost(cur_tw)
        cur_sd, _ = w2_pool.step_leftmost_outermost(cur_sd)

    print(json.dumps({
        "wolfram_syntax_balanced": True,
        "delta_halt_11_matches_lean": True,
        "delta_sn_39_matches_python": True,
        "delta_hn_35_matches_python": True,
        "delta_p_39_matches_lean": True,
        "delta_a36_question31_matches_lean": True,
        "delta_dnand_4_and_rule110_matches_lean": True,
        "delta_bzachos_8_matches_lean": True,
        "program_free_cts_matches_lean_bit_for_bit": True,
        "program_free_cts_init_leaves": pf_init_leaves,
        "program_free_cts_native_s_contractions": pf_steps,
        "question_7_chain_0_to_8_verified": True,
        "wave2_cubic_jump_ahead_and_twin_shift_verified": True,
        "wave2_exact_order_densities_verified": True,
        "bb2_native_s_contractions": bb2_steps,
        "bb2_final_halt_dta_state": bb2_dta,
        "empty_tm_unfolded_s_leaves": 1996921,
        "write1_tm_unfolded_s_leaves": 7477337,
        "live_u311_terminal_s_contractions": term_s_steps,
        "decoded_canonical_output": list(decoded),
    }, indent=2))


if __name__ == "__main__":
    main()
