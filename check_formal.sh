#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"

python3 - <<'PY'
import os, pathlib, re, subprocess, sys

root = pathlib.Path.cwd().resolve()
lean_exe = os.environ.get("LEAN_EXE", "lean")

def strip_comments(src: str) -> str:
    out, i, n, bd, ins = [], 0, len(src), 0, False
    while i < n:
        ch = src[i]
        if ch == "\n": out.append("\n"); i += 1; continue
        if bd > 0:
            if src[i:i+2] == "/-": bd += 1; out.extend([" "," "]); i += 2; continue
            if src[i:i+2] == "-/": bd -= 1; out.extend([" "," "]); i += 2; continue
            out.append(" "); i += 1; continue
        if ins:
            if ch == "\\" and i + 1 < n: out.extend([" "," "]); i += 2; continue
            if ch == '"': ins = False
            out.append(" "); i += 1; continue
        if src[i:i+2] == "/-": bd = 1; out.extend([" "," "]); i += 2; continue
        if src[i:i+2] == "--":
            while i < n and src[i] != "\n": out.append(" "); i += 1
            continue
        if ch == '"': ins = True; out.append(" "); i += 1; continue
        out.append(ch); i += 1
    return "".join(out)

pats = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\s+"),
    "partial": re.compile(r"\bpartial\s+"),
    "unsafe": re.compile(r"\bunsafe\s+"),
    "extern": re.compile(r"@\[extern|\bextern\s+"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Classical.choice": re.compile(r"\bClassical\.choice\b|\bClassical\.em\b|\bopen\s+Classical\b"),
}

visited, order = set(), []
def dfs(p: pathlib.Path):
    p = p.resolve()
    if p in visited: return
    visited.add(p)
    clean = strip_comments(p.read_text(encoding="utf-8"))
    for ln_no, ln in enumerate(clean.splitlines(), 1):
        for k, rx in pats.items():
            if rx.search(ln):
                raise RuntimeError(f"Forbidden token {k} in {p.relative_to(root)}:{ln_no}")
        m = re.match(r"^\s*import\s+([A-Za-z0-9_.]+)", ln)
        if m:
            mod = m.group(1)
            if mod == "Std" or mod.startswith(("Init", "Lean")): continue
            mp = root / (mod.replace(".", "/") + ".lean")
            if not mp.exists(): raise RuntimeError(f"Missing imported module {mod} from {p}")
            dfs(mp)
    order.append(p)

for entry in ["SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean", "s_challenge_master_headline.lean", "TRUST_ZERO_SPEC_CHECK.lean"]:
    dfs(root / entry)

print(f"Static hygiene passed across {len(order)} .lean modules.")
env = os.environ.copy()
env["LEAN_PATH"] = str(root)
for idx, p in enumerate(order, 1):
    olean = p.with_suffix(".olean")
    proc = subprocess.run([lean_exe, "-o", str(olean), str(p)], cwd=str(root), env=env, capture_output=True, text=True, encoding="utf-8")
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + "\n" + proc.stderr)
        sys.exit(proc.returncode)
    if p.name in ("SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean", "s_challenge_master_headline.lean", "TRUST_ZERO_SPEC_CHECK.lean"):
        for ln in proc.stdout.splitlines():
            m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", ln.strip())
            if m:
                axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
                bad = axs - {"propext", "Quot.sound"}
                if bad:
                    raise RuntimeError(f"Disallowed axioms {bad} in {ln}")
print(f"Compiled and verified all {len(order)} Lean 4.33.1 modules cleanly.")
PY

python3 verify_fixed_binary_table.py
python3 verify_lean_u_table.py
lean TRUST_ZERO_SPEC_CHECK.lean
echo "ALL FORMAL LEAN 4.33.1 CHECKS PASSED."
