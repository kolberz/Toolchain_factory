import Frontier24

open WTCF24

-- Must fail: a modulus-5 indexed state has exactly 5 addressable slots.
example : (allFin 5).length = 4 := by
  decide
