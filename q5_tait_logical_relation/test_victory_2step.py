"""Add the 2-step rule `L_s1_2step`:
For `f = S x y` with `x = S u`:
  `(S (S u) y) z -> (S u z) (y z) -> (u (y z)) (z (y z))`!
Whenever `ap(u, y*z)[0] == 37` (and `n2[-1] != 34`), by Left Sink it suffices to prove `HasBot(u * (y * z))`,
where `u` is a STRICT subterm of `f` (`u.size < (S u).size < f.size` AND `u.size < x.size`)!!
Test if ALL 76,699 critical triples are now 100% SOLVED!
"""
from __future__ import annotations
import json
from pathlib import Path
import sys

SPRIZE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SPRIZE))

from hnf_automaton import DELTA_HN as DHN, INF_HN
data = json.loads((SPRIZE / "intrinsic_research" / "productivity_automaton_proof.json").read_text(encoding="utf-8"))
DP = data["table"]
SINK = 37
ZACHOS_P = {14, 32}

reach = {(0, 0)}
wl = [(0, 0)]
while wl:
    a = wl.pop()
    for b in list(reach):
        for x, y in ((a, b), (b, a)):
            nxt = (DP[x[0]][y[0]], DHN[x[1]][y[1]])
            if nxt not in reach:
                reach.add(nxt)
                wl.append(nxt)

def ap(a, b): return (DP[a[0]][b[0]], DHN[a[1]][b[1]])
s0 = (0, 0)
acc = sorted(q for q in reach if q[0] != SINK)
raw_rej = sorted(q for q in reach if q[0] == SINK and q[1] != INF_HN)
all_yz = acc + raw_rej

s1_arg = {q: set() for q in acc}
s2_args = {q: set() for q in acc}
for u in acc:
    q1 = ap(s0, u)
    if q1[0] != SINK:
        s1_arg[q1].add(u)
    for v in acc:
        q2 = ap(q1, v)
        if q2[0] != SINK:
            s2_args[q2].add((u, v))

out_s2 = {(x, z): set() for x in acc for z in acc if ap(x, z)[0] != SINK}
for (x, z), st in out_s2.items():
    for u in s1_arg[x]:
        st.add((u, z))

s2_call_out = {(a, b, w): set() for a in acc for b in acc for w in acc
               if ap(ap(s0, a), b)[0] != SINK and ap(ap(ap(s0, a), b), w)[0] != SINK}
changed = True
while changed:
    changed = False
    for (a, b, w), st_abw in s2_call_out.items():
        f_st = ap(ap(s0, a), b)
        if f_st[0] in ZACHOS_P and w[0] in ZACHOS_P:
            continue
        n1 = ap(a, w)
        n2 = ap(b, w)
        if n1[0] in ZACHOS_P and n2[0] in ZACHOS_P:
            continue
        if a == s0:
            if (w, n2) not in st_abw:
                st_abw.add((w, n2)); changed = True
        for (u1, u2) in out_s2[(a, w)]:
            for res_cd in s2_call_out.get((u1, u2, n2), ()):
                if res_cd not in st_abw:
                    st_abw.add(res_cd); changed = True
    for (x, z), st_xz in out_s2.items():
        if x[0] in ZACHOS_P and z[0] in ZACHOS_P:
            continue
        for (x1, x2) in s2_args[x]:
            for res_cd in s2_call_out.get((x1, x2, z), ()):
                if res_cd not in st_xz:
                    st_xz.add(res_cd); changed = True

nodes = []
for x in acc:
    sx = ap(s0, x)
    for y in all_yz:
        f = ap(sx, y)
        for z in all_yz:
            fz = ap(f, z)
            if fz[0] == SINK and fz[1] != INF_HN:
                nodes.append((x, y, z))
node_set = set(nodes)
sub_of_pval_pair = {}
for (a, b, z) in nodes:
    if b[0] != SINK:
        f = ap(ap(s0, a), b)
        if f[0] != SINK:
            sub_of_pval_pair.setdefault((f, z), []).append((a, b, z))

choices_for = {}
for t in nodes:
    x, y, z = t
    y_is_pval = (y[0] != SINK)
    z_is_pval = (z[0] != SINK)
    n1 = ap(x, z)
    n2 = ap(y, z)
    opts = []

    if n1[1] == INF_HN:
        opts.append(("L_hn34", [], [], []))
    elif n1[0] == SINK and (x[0] == 29 or s2_args[x]):
        opts.append(("L_weak", sub_of_pval_pair.get((x, z), []), sub_of_pval_pair.get((x, z), []), []))

    if n2[1] == INF_HN:
        opts.append(("R_hn34", [], [], []))
    elif n2[0] == SINK and y_is_pval and (y[0] == 29 or s2_args[y]):
        opts.append(("R_weak", sub_of_pval_pair.get((y, z), []), [], []))

    # General C3 (including per-u L_s1_2step optimization when ap(u, n2)[0] == SINK!):
    if n2[1] != INF_HN and x != s0:
        can_do_s1 = True
        f_weaks_2step = []
        x_weaks_s1 = []
        for u in s1_arg[x]:
            un2 = ap(u, n2)
            if un2[1] == INF_HN:
                # u * n2 ALREADY has evalHN == 34 -> Left Sink gives HasBot in 0 subcalls!
                pass
            elif un2[0] == SINK and (u[0] == 29 or s2_args[u] or s1_arg[u]):
                # Wait: if u is s1(w), (S w) * n2 == 37 ONLY if n2[0] == 37 (which needs HasBot(n2), not raw!).
                # So ONLY use L_s1_2step when `u[0] == 29` or (`s2_args[u]` and NOT `s1_arg[u]` and `u != s0`),
                # OR even simpler: at runtime we branch on `u` (`match u with | .s2 a b => L_2step | .zachos => L_2step | _ => step to (u, z, n2)`)!!
                # YES!! At runtime `u : PVal` is concrete!
                # - If `u = .zachos`: `zachos * n2` has HasBot directly (0 subcalls)!
                # - If `u = .s2 a b` and `ap(u, n2)[0] == 37`: `(a, b, n2)` has `1+a.size+b.size = u.size < x.size < f.size` AND `a.size < u.size < x.size`!!
                #   So `(a, b, n2)` shrinks BOTH `f.size` AND `x.size` (just like `L_weak`!)!!
                # - If `u = .s` or `u = .s1 w` (or `ap(u, n2)[0] != 37`): step to `(u, z, n2)` which shrinks `x.size`!
                for (a, b) in s2_args[u]:
                    if ap(ap(ap(s0, a), b), n2)[1] != INF_HN:
                        f_weaks_2step.append((a, b, n2))
                if u == s0 or s1_arg[u]:
                    if ap(ap(ap(s0, u), z), n2)[1] != INF_HN:
                        t3 = (u, z, n2)
                        if t3 in node_set:
                            x_weaks_s1.append(t3)
                        else:
                            can_do_s1 = False
            else:
                if ap(ap(ap(s0, u), z), n2)[1] != INF_HN:
                    t3 = (u, z, n2)
                    if t3 in node_set:
                        x_weaks_s1.append(t3)
                    else:
                        can_do_s1 = False

        can_do_s2 = True
        stricts_s2 = []
        if s2_args[x]:
            if z_is_pval and n1[0] != SINK:
                for (x1, x2) in s2_args[x]:
                    for (a, b) in s2_call_out.get((x1, x2, z), ()):
                        if ap(ap(ap(s0, a), b), n2)[1] != INF_HN:
                            t3 = (a, b, n2)
                            if t3 in node_set:
                                stricts_s2.append(t3)
                            else:
                                can_do_s2 = False
            else:
                can_do_s2 = False

        if can_do_s1 and can_do_s2:
            # Note: `f_weaks_2step` shrinks BOTH `f.size` AND `x.size`!
            opts.append(("C3_2step", f_weaks_2step, f_weaks_2step + x_weaks_s1, stricts_s2))

    choices_for[t] = opts

solved = set()
prev_newly = -1
for R in range(30):
    is_even = (R % 2 == 0)
    cand = {t for t in nodes if choices_for[t]}
    ch = True
    while ch:
        ch = False
        rem = []
        for t in cand:
            if t in solved:
                continue
            ok_t = False
            for (tag, fw, xw, ss) in choices_for[t]:
                if tag == "L_weak":
                    if all(w in cand for w in fw) and all(s in solved for s in ss):
                        ok_t = True; break
                elif is_even:
                    # Wait: in C3_2step, `fw` is `f_weaks_2step` (shrinks BOTH f and x), while `xw` has `f_weaks_2step + x_weaks_s1`!
                    # At EVEN round (shrinks f.size): `f_weaks_2step` can be in `cand`, while `x_weaks_s1` (i.e. xw \ fw) must be in `solved`!
                    xw_only = [w for w in xw if w not in set(fw)]
                    if all(w in cand for w in fw) and all(w in solved for w in xw_only) and all(s in solved for s in ss):
                        ok_t = True; break
                else:
                    # At ODD round (shrinks x.size): ALL of `xw` (both `f_weaks_2step` and `x_weaks_s1`!) shrink `x.size` so can be in `cand`!
                    fw_only = [w for w in fw if w not in set(xw)]
                    if all(w in solved for w in fw_only) and all(w in cand for w in xw) and all(s in solved for s in ss):
                        ok_t = True; break
            if not ok_t:
                rem.append(t)
        if rem:
            cand.difference_update(rem); ch = True
    newly = cand - solved
    solved = cand
    crit_pval_total = sum(1 for t in nodes if t[1][0] != SINK and t[2][0] != SINK)
    crit_pval_solved = sum(1 for t in solved if t[1][0] != SINK and t[2][0] != SINK)
    print(f"Round R={R:2d} ({'EVEN' if is_even else 'ODD '}): pval-crit = {crit_pval_solved} / {crit_pval_total} (all={len(solved)}/{len(nodes)}, +{len(newly)})")
    if crit_pval_solved == crit_pval_total:
        print(f"==> 1000% EUREKA!! ALL {crit_pval_total} / {crit_pval_total} PVAL CRITICAL TRIPLES SOLVED AT MAX RANK R = {R}!!")
        break
    if R >= 2 and len(newly) == 0 and prev_newly == 0:
        uns = [t for t in nodes if t[1][0] != SINK and t[2][0] != SINK and t not in solved]
        print(f"STALLED at {crit_pval_solved}/{crit_pval_total} (remaining={len(uns)}), sample: {uns[:8]}")
        break
    prev_newly = len(newly)
