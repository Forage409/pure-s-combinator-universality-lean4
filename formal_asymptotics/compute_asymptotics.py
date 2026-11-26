"""Exact High-Precision Algebraic & Analytic Combinatorics for Pure-S Phase Transitions.

Computes:
1. Exact integer dynamic programming for leaf sizes n = 1..150 on:
   - Waldmann's 39-state Strong Normalization S-algebra A_SN (sink .sn38),
   - Barendregt-Endrullis-Klop-Waldmann's 35-state Head Normalization S-algebra A_HN (sink .hn34),
   - The 39-state Böhm-Tree Productivity S-algebra A_P (sink .p37),
   - The exact 146-state reachable joint S-algebra Reach(A_P x A_SN x A_HN),
   producing exact integer counts C_{n-1}, #SN(n), #HN(n), #AcceptP(n),
   #(AcceptP & non-SN)(n), #(HN & non-AcceptP)(n), and #INF_HN(n) for n = 1..150.
2. Exact 50+ decimal-place (computed at 130 dps) asymptotic phase-transition constants:
   - Exact rational limiting HNF density c_HN = lim_{n->inf} #HN(n) / C_{n-1}
     = 4429673 / 7077888 = 4429673 / (2^18 * 3^3), derived via exact rational
     evaluation of Y_HN(1/4) and the Perron-Frobenius / Puiseux singular expansion
     Y_q(z) = a_q - b_q * sqrt(1 - 4z) + c_q * (1 - 4z) - d_q * (1 - 4z)^(3/2) + ...,
     verified against exact DP ratios at n = 150.
   - Exact radius of convergence r_SN = 1 / gamma_SN, growth rate gamma_SN < 4,
     asymptotic Catalan ratio prefactor alpha_SN, and exact irreducible integer minimal
     polynomial of r_SN, via exact rational elimination of the 34 lower SCC states
     and exact discriminant factorization on the 4-state top SCC {6, 25, 29, 30}.
   - Exact radius of convergence r_P = 1 / gamma_P, growth rate gamma_P (gamma_SN < gamma_P < 4),
     asymptotic Catalan ratio prefactor alpha_P, and exact irreducible integer minimal
     polynomial of r_P on the 4-state top SCC {18, 24, 29, 33}, proving that among
     productive pure-S combinators, asymptotically 100% (1 - O((gamma_SN/gamma_P)^n))
     are non-halting Zachos-type infinite tree builders.
"""

from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
SPRIZE_ROOT = HERE.parent
if str(SPRIZE_ROOT) not in sys.path:
    sys.path.insert(0, str(SPRIZE_ROOT))

from waldmann_automaton import DELTA as DELTA_SN, INF as SINK_SN
from hnf_automaton import DELTA_HN, INF_HN as SINK_HN

SINK_P = 37


def load_delta_p() -> tuple[tuple[int, ...], ...]:
    p_path = SPRIZE_ROOT / "intrinsic_research" / "productivity_automaton_proof.json"
    raw = json.loads(p_path.read_text(encoding="utf-8"))["table"]
    return tuple(tuple(int(x) for x in row) for row in raw)


def build_joint_146(delta_p, delta_sn, delta_hn):
    """Builds Reach(A_P x A_SN x A_HN) starting from leaf state (0, 0, 0)."""
    reach: list[tuple[int, int, int]] = [(0, 0, 0)]
    seen: dict[tuple[int, int, int], int] = {(0, 0, 0): 0}
    idx = 0
    while idx < len(reach):
        a = reach[idx]
        for j in range(idx + 1):
            b = reach[j]
            for x, y in ((a, b), (b, a)):
                nxt = (delta_p[x[0]][y[0]], delta_sn[x[1]][y[1]], delta_hn[x[2]][y[2]])
                if nxt not in seen:
                    seen[nxt] = len(reach)
                    reach.append(nxt)
        idx += 1
    m = len(reach)
    trans = [
        [
            seen[(delta_p[reach[i][0]][reach[j][0]],
                  delta_sn[reach[i][1]][reach[j][1]],
                  delta_hn[reach[i][2]][reach[j][2]])]
            for j in range(m)
        ]
        for i in range(m)
    ]
    return reach, trans


def run_dp_single(delta: tuple[tuple[int, ...], ...], nmax: int = 150) -> list[list[int]]:
    """Exact integer DP count[q][n] for n = 1..nmax on a single finite S-algebra."""
    m = len(delta)
    dp = [[0] * (nmax + 1) for _ in range(m)]
    rev = [[0] * (nmax + 1) for _ in range(m)]
    dp[0][1] = 1
    rev[0][nmax - 1] = 1
    pairs_for = [[] for _ in range(m)]
    for a in range(m):
        for b in range(m):
            pairs_for[delta[a][b]].append((a, b))
    for n in range(2, nmax + 1):
        lo = nmax - n + 1
        for q in range(m):
            s = 0
            for a, b in pairs_for[q]:
                s += sum(x * y for x, y in zip(dp[a][1:n], rev[b][lo:]))
            dp[q][n] = s
            rev[q][nmax - n] = s
    return dp


def run_dp_cdq_kronecker(trans: list[list[int]], nmax: int = 150) -> list[list[int]]:
    """Exact integer DP on the 146-state joint algebra via CDQ divide-and-conquer + Kronecker big-int."""
    m = len(trans)
    dp = [[0] * (nmax + 1) for _ in range(m)]
    dp[0][1] = 1
    # C_{149} < 4^149 = 2^298; 320 bits per coefficient guarantees zero carry overlap!
    W = 320
    MASK = (1 << W) - 1

    def pack(arr: list[int], start: int, end: int) -> int:
        # Packs arr[start..end] as sum_{i=0}^{end-start} arr[start+i] << (W*i)
        res = 0
        for i in range(end - start, -1, -1):
            res = (res << W) | arr[start + i]
        return res

    def add_unpacked(target_row: list[int], prod: int, offset: int, lo_k: int, hi_k: int) -> None:
        # prod represents sum_{t >= 0} c_t x^(offset + t); extract indices in [lo_k, hi_k]
        start_t = max(0, lo_k - offset)
        end_t = hi_k - offset
        if start_t > end_t or prod == 0:
            return
        cur = prod >> (W * start_t)
        k = offset + start_t
        while cur and k <= hi_k:
            c = cur & MASK
            if c:
                target_row[k] += c
            cur >>= W
            k += 1

    def cdq(lo: int, hi: int) -> None:
        if lo == hi:
            return
        mid = (lo + hi) // 2
        cdq(lo, mid)
        lo_out = mid + 1
        hi_out = hi
        if lo == 1:
            # Convolve [1..mid] x [1..mid] -> [mid+1..hi]
            packed_a = [pack(dp[i], 1, mid) for i in range(m)]
            acc_prod = [0] * m
            for i in range(m):
                pi = packed_a[i]
                if pi == 0:
                    continue
                ti = trans[i]
                for j in range(m):
                    pj = packed_a[j]
                    if pj:
                        acc_prod[ti[j]] += pi * pj
            for q in range(m):
                if acc_prod[q]:
                    add_unpacked(dp[q], acc_prod[q], 2, lo_out, hi_out)
        else:
            # Convolve [lo..mid] x [1..hi-lo] and [1..hi-lo] x [lo..mid] -> [mid+1..hi]
            r_end = hi - lo
            packed_left = [pack(dp[i], lo, mid) for i in range(m)]
            packed_small = [pack(dp[i], 1, r_end) for i in range(m)]
            acc_prod = [0] * m
            for i in range(m):
                pl = packed_left[i]
                ps_i = packed_small[i]
                ti = trans[i]
                if pl:
                    for j in range(m):
                        ps_j = packed_small[j]
                        if ps_j:
                            acc_prod[ti[j]] += pl * ps_j
                if ps_i:
                    for j in range(m):
                        pl_j = packed_left[j]
                        if pl_j:
                            acc_prod[ti[j]] += ps_i * pl_j
            for q in range(m):
                if acc_prod[q]:
                    add_unpacked(dp[q], acc_prod[q], lo + 1, lo_out, hi_out)
        cdq(mid + 1, hi)

    cdq(1, nmax)
    return dp


def solve_hn_exact_puiseux(delta_hn: tuple[tuple[int, ...], ...], work_dps: int = 130):
    """Computes exact rational a_q = Y_q(1/4), stationary distribution pi_q = 2*b_q,
    c_HN = 4429673/7077888, and Puiseux expansion up to u^7 at z = (1 - u^2)/4."""
    mp.mp.dps = work_dps
    m = len(delta_hn)
    pairs = [[] for _ in range(m)]
    for a in range(m):
        for b in range(m):
            pairs[delta_hn[a][b]].append((a, b))

    # Warm-start monotone iteration + Newton with sum(a) = 1/2
    a = [mp.mpf(0)] * m
    for _ in range(3000):
        a = [(mp.mpf("0.25") if q == 0 else mp.mpf(0)) + sum(a[i] * a[j] for i, j in pairs[q]) for q in range(m)]
    for _ in range(20):
        J = mp.matrix(m, m)
        res = mp.matrix(m, 1)
        for q in range(m - 1):
            s = mp.mpf("0.25") if q == 0 else mp.mpf(0)
            for i, j in pairs[q]:
                s += a[i] * a[j]
                J[q, i] += a[j]
                J[q, j] += a[i]
            res[q] = a[q] - s
            for r in range(m):
                J[q, r] = (mp.mpf(1) if r == q else mp.mpf(0)) - J[q, r]
        for r in range(m):
            J[m - 1, r] = mp.mpf(1)
        res[m - 1] = sum(a) - mp.mpf("0.5")
        if mp.norm(res, mp.inf) < mp.mpf("1e-115"):
            break
        da = mp.lu_solve(J, res)
        for r in range(m):
            a[r] -= da[r]

    # Reconstruct exact rationals in sp.QQ and certify algebraic identity!
    a_qq = [sp.Rational(*Fraction(mp.nstr(x, 90)).limit_denominator(10**35).as_integer_ratio()) for x in a]
    for q in range(m):
        rhs = (sp.Rational(1, 4) if q == 0 else sp.Rational(0)) + sum(a_qq[i] * a_qq[j] for i, j in pairs[q])
        assert a_qq[q] == rhs, f"Exact rational check failed at state {q}"
    assert sum(a_qq) == sp.Rational(1, 2)

    # Build exact column-stochastic Jacobian J(a) over QQ
    Ja = sp.zeros(m, m)
    for q in range(m):
        for i, j in pairs[q]:
            Ja[q, i] += a_qq[j]
            Ja[q, j] += a_qq[i]
    for r in range(m):
        assert sum(Ja[q, r] for q in range(m)) == sp.Rational(1)

    M_sys = sp.eye(m) - Ja
    for r in range(m):
        M_sys[m - 1, r] = sp.Rational(1)

    # Puiseux expansion Y_q((1 - u^2)/4) = sum_{k>=0} p[k][q] * u^k
    # Here p[0] = a, p[1] = -b, p[2] = c, p[3] = -d, p[4] = e, p[5] = -f, p[6] = g, p[7] = -h
    # Since sum_q Y_q = (1 - u)/2: sum_q p[0] = 1/2, sum_q p[1] = -1/2, sum_q p[k] = 0 for k >= 2.
    # Equation: p[k][q] = (-1/4 if k==2 and q==0 else 0) + (Ja * p[k])[q] + sum_{j=1}^{k-1} B_q(p[j], p[k-j])
    p_coeffs = [sp.Matrix(a_qq)]
    rhs1 = sp.zeros(m, 1)
    rhs1[m - 1, 0] = sp.Rational(-1, 2)
    p1 = M_sys.LUsolve(rhs1)
    assert (sp.eye(m) - Ja) * p1 == sp.zeros(m, 1)
    p_coeffs.append(p1)

    for k in range(2, 8):
        rhs_k = sp.zeros(m, 1)
        if k == 2:
            rhs_k[0, 0] = sp.Rational(-1, 4)
        for q in range(m):
            conv_q = sp.Rational(0)
            for j in range(1, k):
                pj = p_coeffs[j]
                pkj = p_coeffs[k - j]
                conv_q += sum(pj[u, 0] * pkj[v, 0] for u, v in pairs[q])
            rhs_k[q, 0] += conv_q
        # Fredholm solvability check: sum of rhs_k must be 0!
        assert sum(rhs_k[q, 0] for q in range(m)) == sp.Rational(0)
        rhs_k[m - 1, 0] = sp.Rational(0)
        pk = M_sys.LUsolve(rhs_k)
        p_coeffs.append(pk)

    b_qq = [-p_coeffs[1][q, 0] for q in range(m)]
    pi_qq = [2 * x for x in b_qq]
    c_hn_qq = sum(pi_qq[:34])
    d_hn_qq = -sum(p_coeffs[3][q, 0] for q in range(34))
    f_hn_qq = -sum(p_coeffs[5][q, 0] for q in range(34))
    h_hn_qq = -sum(p_coeffs[7][q, 0] for q in range(34))

    c_hn_mp = mp.mpf(c_hn_qq.p) / mp.mpf(c_hn_qq.q)
    return {
        "c_HN_rational": f"{c_hn_qq.p}/{c_hn_qq.q}",
        "c_HN_numerator": int(c_hn_qq.p),
        "c_HN_denominator": int(c_hn_qq.q),
        "c_HN_denominator_factored": "2^18 * 3^3",
        "non_HN_rational": f"{(1 - c_hn_qq).p}/{(1 - c_hn_qq).q}",
        "c_HN_50dp": mp.nstr(c_hn_mp, 52),
        "c_HN_65dp": mp.nstr(c_hn_mp, 65),
        "non_HN_50dp": mp.nstr(1 - c_hn_mp, 52),
        "d_HN_u3_rational": f"{d_hn_qq.p}/{d_hn_qq.q}",
        "f_HN_u5_rational": f"{f_hn_qq.p}/{f_hn_qq.q}",
        "h_HN_u7_rational": f"{h_hn_qq.p}/{h_hn_qq.q}",
        "a_Y_at_quarter_rational": [f"{x.p}/{x.q}" for x in a_qq],
        "stationary_pi_rational": [f"{x.p}/{x.q}" for x in pi_qq],
        "puiseux_odd_HN": (c_hn_qq, d_hn_qq, f_hn_qq, h_hn_qq),
    }


def poly_rat_add(a, b):
    n1, d1 = a
    n2, d2 = b
    g = sp.gcd(d1, d2)
    num = n1 * (d2 // g) + n2 * (d1 // g)
    den = d1 * (d2 // g)
    g2 = sp.gcd(num, den)
    return (num // g2, den // g2)


def poly_rat_sub(a, b):
    return poly_rat_add(a, (-b[0], b[1]))


def poly_rat_mul(a, b):
    n1, d1 = a
    n2, d2 = b
    g1 = sp.gcd(n1, d2)
    g2 = sp.gcd(n2, d1)
    return ((n1 // g1) * (n2 // g2), (d1 // g2) * (d2 // g1))


def poly_rat_div(a, b):
    return poly_rat_mul(a, (b[1], b[0]))


def solve_sink_algebra_singularity(
    name: str,
    delta: tuple[tuple[int, ...], ...],
    sink: int,
    top_scc: list[int],
    z_guess: str,
    work_dps: int = 130,
):
    """Computes 130-dps singularity r, gamma=1/r, alpha, beta AND exact irreducible minimal polynomial over Z."""
    mp.mp.dps = work_dps
    low_states = [q for q in range(len(delta)) if q != sink and q not in top_scc]
    order = []
    rem = set(low_states)
    while rem:
        for q in list(rem):
            deps = {
                x
                for a in range(len(delta))
                for b in range(len(delta))
                if a != sink and b != sink and delta[a][b] == q
                for x in (a, b)
                if x != q
            }
            if all(d in order for d in deps):
                order.append(q)
                rem.remove(q)

    quad_q = [
        q
        for q in top_scc
        if any(a in top_scc and b in top_scc and delta[a][b] == q for a in top_scc for b in top_scc)
    ][0]
    lin_qs = [q for q in top_scc if q != quad_q]
    idx_lin = {q: i for i, q in enumerate(lin_qs)}

    def eval_numeric(zv):
        Y = {}
        for q in order:
            cp = zv if q == 0 else mp.mpf(0)
            lp = mp.mpf(0)
            for a in range(len(delta)):
                for b in range(len(delta)):
                    if a != sink and b != sink and delta[a][b] == q:
                        if a == q:
                            lp += Y[b]
                        elif b == q:
                            lp += Y[a]
                        else:
                            cp += Y[a] * Y[b]
            Y[q] = cp / (mp.mpf(1) - lp)
        M = mp.eye(3)
        b0 = mp.matrix(3, 1)
        b1 = mp.matrix(3, 1)
        for i, q in enumerate(lin_qs):
            for a in range(len(delta)):
                for b in range(len(delta)):
                    if a != sink and b != sink and delta[a][b] == q:
                        if a in idx_lin:
                            M[i, idx_lin[a]] -= Y[b]
                        elif b in idx_lin:
                            M[i, idx_lin[b]] -= Y[a]
                        elif a == quad_q:
                            b1[i] += Y[b]
                        elif b == quad_q:
                            b1[i] += Y[a]
                        else:
                            b0[i] += Y[a] * Y[b]
        c0_vec = mp.lu_solve(M, b0)
        c1_vec = mp.lu_solve(M, b1)
        C0 = {lin_qs[i]: c0_vec[i] for i in range(3)}
        C1 = {lin_qs[i]: c1_vec[i] for i in range(3)}
        C0[quad_q] = mp.mpf(0)
        C1[quad_q] = mp.mpf(1)
        q2, q1, q0 = mp.mpf(0), mp.mpf(0), mp.mpf(0)
        for a in range(len(delta)):
            for b in range(len(delta)):
                if a != sink and b != sink and delta[a][b] == quad_q:
                    a0, a1 = (C0[a], C1[a]) if a in top_scc else (Y[a], mp.mpf(0))
                    b0_, b1_ = (C0[b], C1[b]) if b in top_scc else (Y[b], mp.mpf(0))
                    q0 += a0 * b0_
                    q1 += a0 * b1_ + a1 * b0_
                    q2 += a1 * b1_
        disc = (mp.mpf(1) - q1) ** 2 - 4 * q2 * q0
        return disc, q2, q1, q0, C0, C1, Y

    r = mp.findroot(lambda zv: eval_numeric(zv)[0], mp.mpf(z_guess))
    disc_r, q2, q1, q0, C0, C1, Y = eval_numeric(r)
    Dp = mp.diff(lambda zv: eval_numeric(zv)[0], r)
    beta = sum(C1[q] for q in top_scc) * mp.sqrt(-r * Dp) / (2 * q2)
    alpha = 2 * beta
    gamma = 1 / r
    amp_n = beta / (2 * mp.sqrt(mp.pi))

    # Verify full 38-state algebraic residual and Jacobian spectral radius at z = r!
    Y_at_r = dict(Y)
    y_quad_r = (mp.mpf(1) - q1) / (2 * q2)
    for q in top_scc:
        Y_at_r[q] = C0[q] + C1[q] * y_quad_r
    acc_states = [q for q in range(len(delta)) if q != sink]
    max_sys_res = mp.mpf(0)
    for q in acc_states:
        rhs = (r if q == 0 else mp.mpf(0)) + sum(
            Y_at_r[a] * Y_at_r[b] for a in acc_states for b in acc_states if delta[a][b] == q
        )
        max_sys_res = max(max_sys_res, abs(Y_at_r[q] - rhs))
    assert max_sys_res < mp.mpf("1e-115"), f"{name}: large system residual {max_sys_res}"

    # Exact integer polynomial elimination over ZZ[z] to extract the exact minimal polynomial of r!
    z = sp.Symbol("z")
    PONE = (sp.Poly(1, z, domain="ZZ"), sp.Poly(1, z, domain="ZZ"))
    PZERO = (sp.Poly(0, z, domain="ZZ"), sp.Poly(1, z, domain="ZZ"))
    PZ = (sp.Poly(z, z, domain="ZZ"), sp.Poly(1, z, domain="ZZ"))

    Yp = {}
    for q in order:
        cp = PZ if q == 0 else PZERO
        lp = PZERO
        for a in range(len(delta)):
            for b in range(len(delta)):
                if a != sink and b != sink and delta[a][b] == q:
                    if a == q:
                        lp = poly_rat_add(lp, Yp[b])
                    elif b == q:
                        lp = poly_rat_add(lp, Yp[a])
                    else:
                        cp = poly_rat_add(cp, poly_rat_mul(Yp[a], Yp[b]))
        Yp[q] = poly_rat_div(cp, poly_rat_sub(PONE, lp))

    Mp = [[PONE if i == j else PZERO for j in range(3)] for i in range(3)]
    B0 = [PZERO] * 3
    B1 = [PZERO] * 3
    for i, q in enumerate(lin_qs):
        for a in range(len(delta)):
            for b in range(len(delta)):
                if a != sink and b != sink and delta[a][b] == q:
                    if a in idx_lin:
                        Mp[i][idx_lin[a]] = poly_rat_sub(Mp[i][idx_lin[a]], Yp[b])
                    elif b in idx_lin:
                        Mp[i][idx_lin[b]] = poly_rat_sub(Mp[i][idx_lin[b]], Yp[a])
                    elif a == quad_q:
                        B1[i] = poly_rat_add(B1[i], Yp[b])
                    elif b == quad_q:
                        B1[i] = poly_rat_add(B1[i], Yp[a])
                    else:
                        B0[i] = poly_rat_add(B0[i], poly_rat_mul(Yp[a], Yp[b]))

    aug = [Mp[i][:] + [B0[i], B1[i]] for i in range(3)]
    for col in range(3):
        piv = next(rw for rw in range(col, 3) if aug[rw][col][0] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        inv_p = aug[col][col]
        aug[col] = [poly_rat_div(x, inv_p) for x in aug[col]]
        for rw in range(3):
            if rw != col and aug[rw][col][0] != 0:
                fac = aug[rw][col]
                aug[rw] = [poly_rat_sub(aug[rw][c], poly_rat_mul(fac, aug[col][c])) for c in range(5)]

    C0p = {lin_qs[i]: aug[i][3] for i in range(3)}
    C1p = {lin_qs[i]: aug[i][4] for i in range(3)}
    C0p[quad_q] = PZERO
    C1p[quad_q] = PONE

    Q2, Q1, Q0 = PZERO, PZERO, PZERO
    for a in range(len(delta)):
        for b in range(len(delta)):
            if a != sink and b != sink and delta[a][b] == quad_q:
                a0, a1 = (C0p[a], C1p[a]) if a in top_scc else (Yp[a], PZERO)
                b0_, b1_ = (C0p[b], C1p[b]) if b in top_scc else (Yp[b], PZERO)
                Q0 = poly_rat_add(Q0, poly_rat_mul(a0, b0_))
                Q1 = poly_rat_add(Q1, poly_rat_add(poly_rat_mul(a0, b1_), poly_rat_mul(a1, b0_)))
                Q2 = poly_rat_add(Q2, poly_rat_mul(a1, b1_))

    Q1m = poly_rat_sub(Q1, PONE)
    lcm_d = sp.lcm(sp.lcm(Q2[1], Q1m[1]), Q0[1])
    Ap = Q2[0] * (lcm_d // Q2[1])
    Bp = Q1m[0] * (lcm_d // Q1m[1])
    Cp = Q0[0] * (lcm_d // Q0[1])
    g = sp.gcd(sp.gcd(Ap, Bp), Cp)
    Ap, Bp, Cp = Ap // g, Bp // g, Cp // g
    disc_poly = Bp * Bp - sp.Poly(4, z, domain="ZZ") * Ap * Cp

    minpoly = None
    minpoly_mult = None
    for fac, mult in disc_poly.factor_list()[1]:
        coeffs = [mp.mpf(int(c)) for c in fac.all_coeffs()]
        val = abs(mp.polyval(coeffs, r))
        if val < mp.mpf("1e-90"):
            minpoly = fac
            minpoly_mult = mult
            break
    assert minpoly is not None and minpoly_mult == 1, f"{name}: failed to isolate simple minpoly of r"

    # Cross-check r to 125 digits directly from minpoly!
    mp_coeffs = [mp.mpf(int(c)) for c in minpoly.all_coeffs()]
    r_from_poly = mp.findroot(lambda x: mp.polyval(mp_coeffs, x), r)
    assert abs(r - r_from_poly) < mp.mpf("1e-120")

    return {
        "r_50dp": mp.nstr(r, 52),
        "r_65dp": mp.nstr(r, 65),
        "gamma_50dp": mp.nstr(gamma, 52),
        "gamma_65dp": mp.nstr(gamma, 65),
        "gamma_over_4_50dp": mp.nstr(gamma / 4, 52),
        "alpha_catalan_ratio_50dp": mp.nstr(alpha, 52),
        "alpha_catalan_ratio_65dp": mp.nstr(alpha, 65),
        "amplitude_raw_50dp": mp.nstr(amp_n, 52),
        "top_scc_states": top_scc,
        "quadratic_pivot_state": quad_q,
        "quadratic_poly_degrees_z": {
            "deg_A": int(Ap.degree()),
            "deg_B": int(Bp.degree()),
            "deg_C": int(Cp.degree()),
        },
        "r_minpoly_degree": int(minpoly.degree()),
        "r_minpoly_coeffs_desc": [int(c) for c in minpoly.all_coeffs()],
        "r_minpoly_expr": str(minpoly.as_expr()),
        "system_residual_at_r": mp.nstr(max_sys_res, 10),
        "raw_mp": (r, gamma, alpha, amp_n, Y_at_r),
    }


def synthesize_lean_integer_certificate(delta, sink: int, p_num: int = 37, q_den: int = 125, scale_d: int = 100000):
    """Synthesizes minimal positive integer weights W_q by monotone least-fixed-point iteration
    at z = p_num / q_den = 37/125 = 0.296 (< r_P < r_SN, so Q/P = 125/37 = 3.378378... < 3.5 < 4):
      D * p_num * [q=0] <= W_q * q_den
      D^2 * p_num * [q=0] + q_den * sum_{delta(a,b)=q} W_a * W_b <= D * W_q * q_den
    for all accepting states q != sink!
    """
    acc = [q for q in range(len(delta)) if q != sink]
    W = {q: 0 for q in acc}
    W[0] = (scale_d * p_num + q_den - 1) // q_den
    for _ in range(5000):
        changed = False
        for q in acc:
            quad_sum = sum(W[a] * W[b] for a in acc for b in acc if delta[a][b] == q)
            lhs2 = (scale_d * scale_d * p_num if q == 0 else 0) + q_den * quad_sum
            denom = scale_d * q_den
            req = (lhs2 + denom - 1) // denom
            if req > W[q]:
                W[q] = req
                changed = True
        if not changed:
            break
    else:
        raise RuntimeError("Integer fixed-point certificate did not converge")
    for q in acc:
        lhs1 = scale_d * p_num * (1 if q == 0 else 0)
        rhs1 = W[q] * q_den
        assert lhs1 <= rhs1, f"Base cert failed at q={q}: {lhs1} > {rhs1}"
        quad_sum = sum(W[a] * W[b] for a in acc for b in acc if delta[a][b] == q)
        lhs2 = (scale_d * scale_d * p_num if q == 0 else 0) + q_den * quad_sum
        rhs2 = scale_d * W[q] * q_den
        assert lhs2 <= rhs2, f"Step cert failed at q={q}: {lhs2} > {rhs2}"
    return {
        "p_num": p_num,
        "q_den": q_den,
        "scale_D": scale_d,
        "sum_W": sum(W.values()),
        "W_by_state": {str(q): W[q] for q in acc},
    }


def main():
    t_start = time.time()
    delta_p = load_delta_p()

    # 1. Build 146-state joint algebra and verify algebraic inclusions
    reach, trans_146 = build_joint_146(delta_p, DELTA_SN, DELTA_HN)
    assert len(reach) == 146
    idx_sn = [i for i, (p, s, h) in enumerate(reach) if s != SINK_SN]
    idx_accp = [i for i, (p, s, h) in enumerate(reach) if p != SINK_P]
    idx_hn = [i for i, (p, s, h) in enumerate(reach) if h != SINK_HN]
    idx_accp_nonsn = [i for i, (p, s, h) in enumerate(reach) if p != SINK_P and s == SINK_SN]
    idx_hn_nonp = [i for i, (p, s, h) in enumerate(reach) if h != SINK_HN and p == SINK_P]
    idx_inf_hn = [i for i, (p, s, h) in enumerate(reach) if h == SINK_HN]

    assert len(idx_sn) == 98
    assert len(idx_accp_nonsn) == 30
    assert len(idx_hn_nonp) == 17
    assert len(idx_inf_hn) == 1
    assert set(idx_sn).issubset(set(idx_accp))
    assert set(idx_accp).issubset(set(idx_hn))

    # 2. Run exact integer DP for n = 1..150 on all 4 algebras!
    nmax = 150
    dp_sn = run_dp_single(DELTA_SN, nmax)
    dp_hn = run_dp_single(DELTA_HN, nmax)
    dp_p = run_dp_single(delta_p, nmax)
    dp_146 = run_dp_cdq_kronecker(trans_146, nmax)

    counts_by_n = []
    for n in range(1, nmax + 1):
        cat_exact = math.comb(2 * n - 2, n - 1) // n
        c_sn_tot = sum(dp_sn[q][n] for q in range(39))
        c_hn_tot = sum(dp_hn[q][n] for q in range(35))
        c_p_tot = sum(dp_p[q][n] for q in range(39))
        c_146_tot = sum(dp_146[i][n] for i in range(146))
        assert cat_exact == c_sn_tot == c_hn_tot == c_p_tot == c_146_tot

        sn_n = sum(dp_sn[q][n] for q in range(38))
        hn_n = sum(dp_hn[q][n] for q in range(34))
        inf_hn_n = dp_hn[34][n]
        accp_n = sum(dp_p[q][n] for q in range(39) if q != SINK_P)

        # Cross-verify every class against the 146-state joint DP!
        assert sn_n == sum(dp_146[i][n] for i in idx_sn)
        assert hn_n == sum(dp_146[i][n] for i in idx_hn)
        assert inf_hn_n == sum(dp_146[i][n] for i in idx_inf_hn)
        assert accp_n == sum(dp_146[i][n] for i in idx_accp)

        accp_nonsn_n = sum(dp_146[i][n] for i in idx_accp_nonsn)
        hn_nonp_n = sum(dp_146[i][n] for i in idx_hn_nonp)
        assert accp_nonsn_n == accp_n - sn_n
        assert hn_nonp_n == hn_n - accp_n
        assert sn_n + accp_nonsn_n + hn_nonp_n + inf_hn_n == cat_exact

        counts_by_n.append({
            "n": n,
            "catalan": str(cat_exact),
            "SN": str(sn_n),
            "AcceptP": str(accp_n),
            "HN": str(hn_n),
            "AcceptP_nonSN": str(accp_nonsn_n),
            "HN_nonAcceptP": str(hn_nonp_n),
            "INF_HN": str(inf_hn_n),
        })

    # 3. High-precision asymptotic constants (130 working dps -> 50+ certified digits)
    hn_res = solve_hn_exact_puiseux(DELTA_HN, work_dps=130)
    sn_res = solve_sink_algebra_singularity(
        "A_SN", DELTA_SN, SINK_SN, [6, 25, 29, 30], "0.29674299328035902", work_dps=130
    )
    p_res = solve_sink_algebra_singularity(
        "A_P", delta_p, SINK_P, [18, 24, 29, 33], "0.29673733243763366", work_dps=130
    )

    mp.mp.dps = 130
    r_sn, gamma_sn, alpha_sn, amp_sn, _ = sn_res.pop("raw_mp")
    r_p, gamma_p, alpha_p, amp_p, _ = p_res.pop("raw_mp")
    c_hn_qq, d_hn_qq, f_hn_qq, h_hn_qq = hn_res.pop("puiseux_odd_HN")

    # 4. Cross-check analytical asymptotics against exact n = 150 DP ratios!
    c150 = int(counts_by_n[149]["catalan"])
    hn150 = int(counts_by_n[149]["HN"])
    sn149 = int(counts_by_n[148]["SN"])
    sn150 = int(counts_by_n[149]["SN"])
    p149 = int(counts_by_n[148]["AcceptP"])
    p150 = int(counts_by_n[149]["AcceptP"])

    hn150_ratio = mp.mpf(hn150) / mp.mpf(c150)
    # Exact Flajolet-Sedgewick / binomial transfer at n = 150 up to u^7:
    # [z^n](-u)/C_{n-1} = 2
    # [z^n](-u^3)/C_{n-1} = -6 / (2n - 3)
    # [z^n](-u^5)/C_{n-1} = 30 / ((2n - 3)(2n - 5))
    # [z^n](-u^7)/C_{n-1} = -210 / ((2n - 3)(2n - 5)(2n - 7))
    n_val = 150
    hn150_puiseux_pred_qq = (
        c_hn_qq
        - sp.Rational(6, 2 * n_val - 3) * d_hn_qq
        + sp.Rational(30, (2 * n_val - 3) * (2 * n_val - 5)) * f_hn_qq
        - sp.Rational(210, (2 * n_val - 3) * (2 * n_val - 5) * (2 * n_val - 7)) * h_hn_qq
    )
    hn150_puiseux_pred = mp.mpf(hn150_puiseux_pred_qq.p) / mp.mpf(hn150_puiseux_pred_qq.q)
    hn150_puiseux_err = abs(hn150_ratio - hn150_puiseux_pred)

    sn_raw_ratio_150 = mp.mpf(sn150) / mp.mpf(sn149)
    sn_darboux_gamma_150 = sn_raw_ratio_150 / (mp.mpf(1) - mp.mpf(3) / mp.mpf(2 * 150))
    p_raw_ratio_150 = mp.mpf(p150) / mp.mpf(p149)
    p_darboux_gamma_150 = p_raw_ratio_150 / (mp.mpf(1) - mp.mpf(3) / mp.mpf(2 * 150))

    sn_cat_asymp_150 = alpha_sn * (gamma_sn / 4) ** 150
    sn_cat_exact_150 = mp.mpf(sn150) / mp.mpf(c150)
    p_cat_asymp_150 = alpha_p * (gamma_p / 4) ** 150
    p_cat_exact_150 = mp.mpf(p150) / mp.mpf(c150)

    # 5. Synthesize exact integer certificate at z = 37/125 = 0.296 for Lean 4 exponential decay theorem!
    cert_sn = synthesize_lean_integer_certificate(DELTA_SN, SINK_SN, p_num=37, q_den=125, scale_d=100000)
    cert_p = synthesize_lean_integer_certificate(delta_p, SINK_P, p_num=37, q_den=125, scale_d=100000)

    elapsed = time.time() - t_start

    output = {
        "metadata": {
            "description": "Exact Pure-S Combinator Asymptotic Phase-Transition Census (n=1..150) and 50+ Digit Analytic Combinatorics Constants",
            "n_max": nmax,
            "working_decimal_precision": 130,
            "reported_decimal_precision": 50,
            "elapsed_seconds": round(elapsed, 3),
        },
        "joint_146_algebra_partition": {
            "total_reachable_triples": 146,
            "SN_states": 98,
            "AcceptP_and_nonSN_states": 30,
            "HN_and_nonAcceptP_states": 17,
            "INF_HN_states": 1,
            "strict_inclusions_verified": "SN (98) < AcceptP (128) < HN (145) < All (146)",
            "minimal_witness_sizes": {
                "first_non_SN_size": next(row["n"] for row in counts_by_n if int(row["SN"]) < int(row["catalan"])),
                "first_non_AcceptP_size": next(row["n"] for row in counts_by_n if int(row["AcceptP"]) < int(row["catalan"])),
                "first_INF_HN_size": next(row["n"] for row in counts_by_n if int(row["INF_HN"]) > 0),
                "first_AcceptP_nonSN_size": next(row["n"] for row in counts_by_n if int(row["AcceptP_nonSN"]) > 0),
            },
        },
        "asymptotic_constants_50dp": {
            "HN_phase": hn_res,
            "SN_phase": sn_res,
            "AcceptP_phase": p_res,
            "phase_separation_constants": {
                "gamma_P_minus_gamma_SN_50dp": mp.nstr(gamma_p - gamma_sn, 52),
                "gamma_SN_over_gamma_P_50dp": mp.nstr(gamma_sn / gamma_p, 52),
                "alpha_SN_over_alpha_P_50dp": mp.nstr(alpha_sn / alpha_p, 52),
                "zachos_dominance_half_life_leaves": float(mp.log(2) / mp.log(gamma_p / gamma_sn)),
            },
        },
        "n150_empirical_verification": {
            "HN_over_Catalan_exact_n150": mp.nstr(hn150_ratio, 52),
            "c_HN_limit_50dp": hn_res["c_HN_50dp"],
            "HN_n150_minus_c_HN": mp.nstr(hn150_ratio - (mp.mpf(c_hn_qq.p) / mp.mpf(c_hn_qq.q)), 20),
            "HN_puiseux_u7_prediction_n150": mp.nstr(hn150_puiseux_pred, 52),
            "HN_puiseux_u7_abs_error_n150": mp.nstr(hn150_puiseux_err, 12),
            "SN_ratio_150_over_149_raw": mp.nstr(sn_raw_ratio_150, 35),
            "SN_ratio_150_over_149_darboux_corrected": mp.nstr(sn_darboux_gamma_150, 35),
            "gamma_SN_exact": mp.nstr(gamma_sn, 35),
            "SN_darboux_rel_error_n150": mp.nstr(abs(sn_darboux_gamma_150 - gamma_sn) / gamma_sn, 12),
            "SN_over_Catalan_exact_n150": mp.nstr(sn_cat_exact_150, 30),
            "SN_over_Catalan_leading_asymp_n150": mp.nstr(sn_cat_asymp_150, 30),
            "AcceptP_ratio_150_over_149_raw": mp.nstr(p_raw_ratio_150, 35),
            "AcceptP_ratio_150_over_149_darboux_corrected": mp.nstr(p_darboux_gamma_150, 35),
            "gamma_P_exact": mp.nstr(gamma_p, 35),
            "AcceptP_darboux_rel_error_n150": mp.nstr(abs(p_darboux_gamma_150 - gamma_p) / gamma_p, 12),
            "AcceptP_over_Catalan_exact_n150": mp.nstr(p_cat_exact_150, 30),
            "AcceptP_over_Catalan_leading_asymp_n150": mp.nstr(p_cat_asymp_150, 30),
        },
        "lean_exponential_decay_certificates_z_37_125": {
            "A_SN": cert_sn,
            "A_P": cert_p,
        },
        "exact_counts_n_1_to_150": counts_by_n,
    }

    const_path = HERE / "asymptotic_constants.json"
    res_path = HERE / "asymptotic_results.json"
    const_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    res_path.write_text(json.dumps(output, indent=2), encoding="utf-8")

    print(f"Completed exact n=1..150 DP + 50-digit constants in {elapsed:.2f}s!")
    print(f"  Minimal witness sizes: {output['joint_146_algebra_partition']['minimal_witness_sizes']}")
    print(f"  c_HN     = {hn_res['c_HN_rational']} = {hn_res['c_HN_50dp']}")
    print(f"  #HN(150)/C_149         = {mp.nstr(hn150_ratio, 25)}")
    print(f"  Puiseux u^7 at n=150   = {mp.nstr(hn150_puiseux_pred, 25)} (err = {mp.nstr(hn150_puiseux_err, 6)})")
    print(f"  r_SN     = {sn_res['r_50dp']} (minpoly deg = {sn_res['r_minpoly_degree']})")
    print(f"  gamma_SN = {sn_res['gamma_50dp']}")
    print(f"  Darboux SN(150)/SN(149)= {mp.nstr(sn_darboux_gamma_150, 25)}")
    print(f"  r_P      = {p_res['r_50dp']} (minpoly deg = {p_res['r_minpoly_degree']})")
    print(f"  gamma_P  = {p_res['gamma_50dp']}")
    print(f"  Darboux P(150)/P(149)  = {mp.nstr(p_darboux_gamma_150, 25)}")


if __name__ == "__main__":
    main()
