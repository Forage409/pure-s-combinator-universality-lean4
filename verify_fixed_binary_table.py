"""Confirm the Lean table exactly matches the live fixed binary compiler."""
import re
from pathlib import Path
from prize_encoder import BINARY_UNIVERSAL

pattern=re.compile(r'\{ q := (\d+), read := (true|false), next := (\d+), write := (true|false), move := (-?\d+) \}')
text=Path('fixed_binary_table.lean').read_text(encoding='utf-8')
rows=pattern.findall(text)
assert len(rows)==len(BINARY_UNIVERSAL)==262
seen=set()
for q,b,n,w,m in rows:
    key=(int(q),int(b=='true'))
    assert key not in seen
    seen.add(key)
    actual=BINARY_UNIVERSAL[key]
    assert (actual.next_state,actual.write,actual.move)==(int(n),int(w=='true'),int(m))
assert seen==set(BINARY_UNIVERSAL)
print('Lean transition table matches all 262 entries from the executable compiler')
