import Lean

/-
  PortableLean_Strengthened.lean
  Lean-core-only candidate; no Mathlib import.

  The statements deliberately avoid claiming a general 3D parallelepiped
  theorem, a Syracuse dynamical result, or a Nash equilibrium without the
  missing mathematical data.
-/

namespace PortableLean

/-! ## 1. Core dependent-type and arithmetic invariants -/

theorem poly_id (α : Type) (x : α) : x = x := rfl
theorem modus_ponens (P Q : Prop) (h : P → Q) (hp : P) : Q := h hp
theorem church_2_plus_2 : 2 + 2 = 4 := rfl

/-! ## 2. Catalytic shear: restoration plus output-register computation -/

structure Reg3 where
  O : Int
  u : Int
  v : Int
  deriving Repr, DecidableEq

def catalyticShearStep (s : Reg3) (x3 cx4 : Int) : Reg3 :=
  let u1 := s.u + x3
  let v1 := s.v + cx4
  let O1 := s.O + u1 * v1
  let u2 := u1 - x3
  let O2 := O1 - u2 * v1
  let v2 := v1 - cx4
  let u3 := u2 + x3
  let O3 := O2 - u3 * v2
  let u4 := u3 - x3
  let O4 := O3 + u4 * v2
  { O := O4, u := u4, v := v2 }

theorem catalytic_restores_u (s : Reg3) (x3 cx4 : Int) :
    (catalyticShearStep s x3 cx4).u = s.u := by
  simp [catalyticShearStep]

theorem catalytic_restores_v (s : Reg3) (x3 cx4 : Int) :
    (catalyticShearStep s x3 cx4).v = s.v := by
  simp [catalyticShearStep]

/-- The net output increment is x3 * cx4; no interpretation is assumed. -/
theorem catalytic_computes_product (s : Reg3) (x3 cx4 : Int) :
    (catalyticShearStep s x3 cx4).O = s.O + x3 * cx4 := by
  simp [catalyticShearStep, Int.add_mul, Int.mul_add, Int.sub_eq_add_neg,
    Int.neg_mul, Int.mul_neg]
  omega

/-! ## 3. Ternary packing: exact capacity and explicit slack -/

theorem ternary_4trits_fit_7bits : 3 ^ 4 < 2 ^ 7 := by decide
theorem ternary_4trits_capacity_values : 3 ^ 4 = 81 ∧ 2 ^ 7 = 128 := by decide
theorem ternary_4trits_capacity_slack : 3 ^ 4 + 47 = 2 ^ 7 := by decide

/-! ## 4. Syracuse weight: exact formula at a=1, no dynamical claim -/

def syracuseWeight (a : Nat) : Int := 4 - (2 ^ a : Int)
theorem syracuse_weight_at_one : syracuseWeight 1 = 2 := by decide
theorem syracuse_sevenfold_weight_at_one : 7 * syracuseWeight 1 = 14 := by decide

/-! ## 5. Coordinatewise integer-cube covering, not arbitrary parallelepipeds -/

theorem hadwiger_1d_cover (x : Int) (hx1 : -3 ≤ x) (hx2 : x ≤ 3) :
    (let s : Int := if 0 ≤ x then 1 else -1;
     -2 ≤ x - s ∧ x - s ≤ 2) := by
  split <;> omega

structure Int3 where
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq

def cubeCoverShift (p : Int3) : Int3 :=
  { x := if 0 ≤ p.x then 1 else -1
    y := if 0 ≤ p.y then 1 else -1
    z := if 0 ≤ p.z then 1 else -1 }

theorem hadwiger_integer_cube_cover (p : Int3)
    (hx1 : -3 ≤ p.x) (hx2 : p.x ≤ 3)
    (hy1 : -3 ≤ p.y) (hy2 : p.y ≤ 3)
    (hz1 : -3 ≤ p.z) (hz2 : p.z ≤ 3) :
    -2 ≤ p.x - (cubeCoverShift p).x ∧ p.x - (cubeCoverShift p).x ≤ 2 ∧
    -2 ≤ p.y - (cubeCoverShift p).y ∧ p.y - (cubeCoverShift p).y ≤ 2 ∧
    -2 ≤ p.z - (cubeCoverShift p).z ∧ p.z - (cubeCoverShift p).z ≤ 2 := by
  have hx := hadwiger_1d_cover p.x hx1 hx2
  have hy := hadwiger_1d_cover p.y hy1 hy2
  have hz := hadwiger_1d_cover p.z hz1 hz2
  constructor
  · simpa [cubeCoverShift] using hx.1
  constructor
  · simpa [cubeCoverShift] using hx.2
  constructor
  · simpa [cubeCoverShift] using hy.1
  constructor
  · simpa [cubeCoverShift] using hy.2
  constructor
  · simpa [cubeCoverShift] using hz.1
  · simpa [cubeCoverShift] using hz.2

/-! ## 6. Nash-style regret threshold: arithmetic certificate only -/

def isFifthNash (regret1 regret2 maxPayoffScale : Int) : Prop :=
  5 * regret1 ≤ maxPayoffScale ∧ 5 * regret2 ≤ maxPayoffScale

theorem sample_regret_threshold_certificate :
    isFifthNash 120000 120000 1000000 := by
  unfold isFifthNash
  omega

/-! ## 7. Integer scaled-cosine bound: non-strict linear and squared inequalities -/

theorem oblique_chordal_linear_bound (R c : Nat) (hc : c ≤ 1000) :
    R * c ≤ R * 1000 := Nat.mul_le_mul_left R hc

theorem oblique_chordal_squared_bound (R c : Nat) (hc : c ≤ 1000) :
    (R * c) * (R * c) ≤ (R * 1000) * (R * 1000) := by
  have h := Nat.mul_le_mul_left R hc
  exact Nat.mul_le_mul h h

end PortableLean
