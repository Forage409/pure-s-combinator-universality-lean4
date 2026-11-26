param([switch]$FullCases)
$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$env:LEAN_PATH = $PSScriptRoot
$bundledLean = Join-Path $PSScriptRoot 'tools\lean-4.33.1-windows\bin\lean.exe'
if (Test-Path $bundledLean) {
  $lean = $bundledLean
} else {
  $leanCmd = Get-Command lean -ErrorAction SilentlyContinue
  if (-not $leanCmd) { throw 'Lean 4.33.1 executable not found (install elan with lean-toolchain or place tools\lean-4.33.1-windows).' }
  $lean = $leanCmd.Source
}
$env:LEAN_EXE_RESOLVED = $lean

# 1. Static hygiene & topological .olean check across the full transitive import graph of s_challenge_master_headline.lean
$pyScript = @'
import pathlib, re, subprocess, os, sys
root = pathlib.Path.cwd().resolve()
lean_exe = pathlib.Path(os.environ["LEAN_EXE_RESOLVED"])

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

master = root / "s_challenge_master_headline.lean"
dfs(master)
print(f"Static hygiene passed across all {len(order)} transitive .lean modules (zero sorry/admit/axiom/native_decide/Classical.choice).")

env = os.environ.copy()
env["LEAN_PATH"] = str(root)
rebuilt = 0
for p in order:
    olean = p.with_suffix(".olean")
    need = (p == master) or (not olean.exists()) or (olean.stat().st_mtime + 1e-6 < p.stat().st_mtime)
    if need:
        proc = subprocess.run([str(lean_exe), "-o", str(olean), str(p)], cwd=str(root), env=env, capture_output=True, text=True, encoding="utf-8")
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout + "\n" + proc.stderr)
            raise RuntimeError(f"Lean compilation failed on {p.relative_to(root)}")
        if p == master:
            for ln in proc.stdout.splitlines():
                ln = ln.strip()
                if not ln: continue
                print(" ", ln)
                m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", ln)
                if m:
                    axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
                    bad = axs - {"propext", "Quot.sound"}
                    if bad: raise RuntimeError(f"Disallowed axioms {bad} in {ln}")
        rebuilt += 1
print(f"Verified all {len(order)} .olean artifacts up-to-date ({rebuilt} compiled).")
'@
$pyScript | python -X utf8 -
if ($LASTEXITCODE -ne 0) { throw 'Transitive Lean master headline check failed' }

# 2. Executable table parity checks
python -X utf8 verify_fixed_binary_table.py
if ($LASTEXITCODE -ne 0) { throw 'Executable binary table mismatch' }
python -X utf8 verify_lean_u_table.py
if ($LASTEXITCODE -ne 0) { throw 'Executable U table mismatch' }

if ($FullCases) {
  foreach ($case in Get-ChildItem -LiteralPath 'formal_cases' -Filter '*.lean') {
    & $lean -o ([IO.Path]::ChangeExtension($case.FullName,'.olean')) $case.FullName | Out-Null
    if ($LASTEXITCODE -ne 0) { throw "Lean check failed: $($case.Name)" }
  }
  foreach ($module in @('all_binary_finite_cases','all_binary_context_cases')) {
    & $lean "$module.lean" | Out-Null
    if ($LASTEXITCODE -ne 0) { throw "Lean check failed: $module" }
  }
}

& $lean 'u_to_s_endpoint.lean' | Select-Object -Last 2
if ($LASTEXITCODE -ne 0) { throw 'Endpoint check failed' }
Write-Output 'ALL FORMAL LEAN 4.33.1 CHECKS PASSED.'
