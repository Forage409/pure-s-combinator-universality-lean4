"""Confirm Lean's 32-row U(3,11) table in fixed_u_program.lean agrees with the executable table."""
import re
from pathlib import Path
from neary_u3_11 import machine

DIR_MAP = {".left": -1, ".stay": 0, ".right": 1}
pattern = re.compile(r"\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*some\s*⟨(\d+),(\d+),(\.[a-z]+)⟩")
rows = pattern.findall(Path("fixed_u_program.lean").read_text(encoding="utf-8"))
table = machine()
assert len(rows) == len(table) == 32
seen = set()
for q, a, wr, nxt, d_str in rows:
    key = (int(q), int(a))
    assert key not in seen
    seen.add(key)
    r = table[key]
    assert (r.next_state, r.write, r.move) == (int(nxt), int(wr), DIR_MAP[d_str])
assert seen == set(table)
print("Lean U(3,11) table matches all 32 executable rows")
