import Frontier24

open WTCF24

-- Must fail: cost-aware selection chooses modulus 5, not the first-success modulus 4.
example : (chooseCosted decisiveVals decisiveTarget frontier23Order).map (fun c => c.modulus) = some 4 := by
  decide
