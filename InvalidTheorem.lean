import Mathlib

-- This file must be rejected. A zero exit code invalidates the certificate.
example : (1 : Nat) = 2 := by
  rfl
