import Frontier24

open WTCF24

-- Must fail: target residue 3 is absent modulo 5 for [1,5].
example : indexedRun 5 decisiveVals ⟨3, by decide⟩ = true := by
  decide
