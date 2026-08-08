import Mathlib

example (n : Nat) : n + 0 = n := by
  simp

example : (21 : Nat) * 2 = 42 := by
  norm_num

example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  aesop

example (x y : Int) (h : x ≤ y) : x ≤ y + 1 := by
  omega
