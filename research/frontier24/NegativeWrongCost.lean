import Frontier24

open WTCF24

-- Must fail: modulus 4 has predicted certificate cost 10 on the decisive family.
example : certificateCost 4 (indexedRun 4 decisiveVals) = 9 := by
  decide
