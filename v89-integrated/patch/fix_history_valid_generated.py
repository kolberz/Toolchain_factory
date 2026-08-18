from pathlib import Path
import sys

path = Path(sys.argv[1])
s = path.read_text()
old = "simp [lookupSkipCostFrom, historyLookupLoopConfig processedLiterals processedWidth]"
new = "simp [lookupSkipCostFrom, historyLookupLoopConfig]"
if old not in s:
    raise SystemExit("expected generated simp pattern not found")
s = s.replace(old, new, 1)
path.write_text(s)
print(path)
