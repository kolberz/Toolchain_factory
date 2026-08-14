import Std

namespace WTCF24

/-- Exact natural-number value selected by Boolean source bits. -/
def selectedValue : List Bool → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | b :: bs, v :: vs => (if b then v else 0) + selectedValue bs vs

/-- Fixed-size indexed residue state. There are exactly `m` addressable slots. -/
abbrev ResidueState (m : Nat) := Fin m → Bool

/-- Canonical enumeration of every slot in a fixed-size residue state. -/
def allFin (m : Nat) : List (Fin m) := List.ofFn (fun i : Fin m => i)

@[simp] theorem allFin_length (m : Nat) : (allFin m).length = m := by
  simp [allFin]

/-- Empty-subset state. -/
def initialState (m : Nat) : ResidueState m :=
  fun r => decide (r.val = 0)

/-- One fixed-index transition. For each destination residue, scan all predecessor slots. -/
def indexedStep (m v : Nat) (s : ResidueState m) : ResidueState m :=
  fun r =>
    s r || (allFin m).any (fun q =>
      s q && decide ((v + q.val) % m = r.val))

/-- Executable fixed-state residue DP. -/
def indexedRun (m : Nat) : List Nat → ResidueState m
  | [] => initialState m
  | v :: vs => indexedStep m v (indexedRun m vs)

/-- Exact source semantics at one residue. -/
def ExactReachable (m : Nat) (vals : List Nat) (r : Fin m) : Prop :=
  ∃ bits : List Bool,
    bits.length = vals.length ∧ selectedValue bits vals % m = r.val

/-- `any` over `allFin` is exact existential search over the indexed state. -/
theorem any_allFin_true_iff {m : Nat} {p : Fin m → Bool} :
    (allFin m).any p = true ↔ ∃ q : Fin m, p q = true := by
  simp [allFin]

/-- One implementation transition has the expected skip/take semantics. -/
theorem indexedStep_true_iff {m v : Nat} {s : ResidueState m} {r : Fin m} :
    indexedStep m v s r = true ↔
      s r = true ∨
        ∃ q : Fin m, s q = true ∧ (v + q.val) % m = r.val := by
  constructor
  · intro h
    have hor : s r = true ∨
        (allFin m).any (fun q => s q && decide ((v + q.val) % m = r.val)) = true := by
      simpa [indexedStep] using h
    rcases hor with hr | ha
    · exact Or.inl hr
    · right
      rcases any_allFin_true_iff.mp ha with ⟨q, hq⟩
      have hb : s q = true ∧ decide ((v + q.val) % m = r.val) = true := by
        simpa only [Bool.and_eq_true] using hq
      exact ⟨q, hb.1, of_decide_eq_true hb.2⟩
  · intro h
    have hor : s r = true ∨
        (allFin m).any (fun q => s q && decide ((v + q.val) % m = r.val)) = true := by
      rcases h with hr | ht
      · exact Or.inl hr
      · rcases ht with ⟨q, hsq, hmod⟩
        right
        apply any_allFin_true_iff.mpr
        refine ⟨q, ?_⟩
        simp only [Bool.and_eq_true]
        exact ⟨hsq, decide_eq_true hmod⟩
    simpa [indexedStep] using hor

/-- Exact source semantics obey the same skip/take recurrence as the indexed transition. -/
theorem exactReachable_cons {m v : Nat} (hm : 0 < m) (vals : List Nat) (r : Fin m) :
    ExactReachable m (v :: vals) r ↔
      ExactReachable m vals r ∨
        ∃ q : Fin m, ExactReachable m vals q ∧ (v + q.val) % m = r.val := by
  constructor
  · rintro ⟨bits, hlen, hsum⟩
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
        have hlen' : bs.length = vals.length := by
          simpa using hlen
        cases b with
        | false =>
            left
            exact ⟨bs, hlen', by simpa [selectedValue] using hsum⟩
        | true =>
            right
            let q : Fin m := ⟨selectedValue bs vals % m, Nat.mod_lt _ hm⟩
            refine ⟨q, ⟨bs, hlen', rfl⟩, ?_⟩
            change (v + (selectedValue bs vals % m)) % m = r.val
            simpa [selectedValue, Nat.add_mod] using hsum
  · intro h
    rcases h with hskip | htake
    · rcases hskip with ⟨bs, hlen, hsum⟩
      refine ⟨false :: bs, by simp [hlen], ?_⟩
      simpa [selectedValue] using hsum
    · rcases htake with ⟨q, hq, hstep⟩
      rcases hq with ⟨bs, hlen, hsum⟩
      refine ⟨true :: bs, by simp [hlen], ?_⟩
      calc
        selectedValue (true :: bs) (v :: vals) % m
            = (v + q.val) % m := by
                simp [selectedValue, Nat.add_mod, hsum, Nat.mod_eq_of_lt q.isLt]
        _ = r.val := hstep

/-- Main Frontier-24 semantic theorem: every bit in the fixed-size implementation is
    true exactly when an actual Boolean subset selector realizes that residue. -/
theorem indexedRun_exact {m : Nat} (hm : 0 < m) (vals : List Nat) (r : Fin m) :
    indexedRun m vals r = true ↔ ExactReachable m vals r := by
  induction vals generalizing r with
  | nil =>
      simp [indexedRun, initialState, ExactReachable, selectedValue, eq_comm]
  | cons v vs ih =>
      rw [indexedRun, indexedStep_true_iff, exactReachable_cons hm]
      constructor
      · intro h
        rcases h with hskip | htake
        · exact Or.inl ((ih r).mp hskip)
        · rcases htake with ⟨q, hq, hstep⟩
          exact Or.inr ⟨q, (ih q).mp hq, hstep⟩
      · intro h
        rcases h with hskip | htake
        · exact Or.inl ((ih r).mpr hskip)
        · rcases htake with ⟨q, hq, hstep⟩
          exact Or.inr ⟨q, (ih q).mpr hq, hstep⟩

/-- Explicit one-step preservation corollary. -/
theorem one_transition_preserves_exact {m v : Nat} (hm : 0 < m)
    (vals : List Nat) (r : Fin m) :
    indexedStep m v (indexedRun m vals) r = true ↔
      ExactReachable m (v :: vals) r := by
  simpa [indexedRun] using indexedRun_exact hm (v :: vals) r

/-- A full materialized transition evaluates `m` destinations against `m` predecessors. -/
def transitionWork (m : Nat) : Nat := m * m

/-- Work model for fully materializing every state after every source value. -/
def fullRunWork (m : Nat) : List Nat → Nat
  | [] => 0
  | _ :: vs => fullRunWork m vs + transitionWork m

/-- The transition work is exactly the square of the fixed slot count. -/
theorem transitionWork_from_slots (m : Nat) :
    transitionWork m = (allFin m).length * (allFin m).length := by
  simp [transitionWork]

/-- Kernel-checked polynomial work bound/equality for the explicit materialization model. -/
theorem fullRunWork_exact (m : Nat) (vals : List Nat) :
    fullRunWork m vals = vals.length * (m * m) := by
  induction vals with
  | nil => simp [fullRunWork]
  | cons v vs ih =>
      simp [fullRunWork, transitionWork, ih, Nat.succ_mul, Nat.add_comm]

/-- Count true bits in the indexed state. -/
def activeCount (m : Nat) (s : ResidueState m) : Nat :=
  (allFin m).foldl (fun n r => if s r then n + 1 else n) 0

/-- Predicted proof-certificate cost: fixed state metadata plus two units per active residue. -/
def certificateCost (m : Nat) (s : ResidueState m) : Nat :=
  m + 2 * activeCount m s

/-- Canonical target index for a positive modulus. -/
def targetFin (m : Nat) (hm : 0 < m) (target : Nat) : Fin m :=
  ⟨target % m, Nat.mod_lt _ hm⟩

/-- Proof-producing, cost-carrying residue obstruction. -/
structure CostedObstruction (vals : List Nat) (target : Nat) where
  modulus : Nat
  positive : 0 < modulus
  targetAbsent : indexedRun modulus vals (targetFin modulus positive target) = false
  cost : Nat
  cost_eq : cost = certificateCost modulus (indexedRun modulus vals)

/-- Executable constructor for a costed obstruction at one modulus. -/
def tryCosted (vals : List Nat) (target m : Nat) : Option (CostedObstruction vals target) :=
  if hm : 0 < m then
    let idx := targetFin m hm target
    if h : indexedRun m vals idx = false then
      some {
        modulus := m
        positive := hm
        targetAbsent := h
        cost := certificateCost m (indexedRun m vals)
        cost_eq := rfl
      }
    else none
  else none

/-- A costed residue certificate rules out every exact subset witness. -/
theorem no_exact_witness_of_costed {vals : List Nat} {target : Nat}
    (c : CostedObstruction vals target) :
    ¬ ∃ bits : List Bool,
      bits.length = vals.length ∧ selectedValue bits vals = target := by
  rintro ⟨bits, hlen, hsum⟩
  let idx := targetFin c.modulus c.positive target
  have hex : ExactReachable c.modulus vals idx := by
    refine ⟨bits, hlen, ?_⟩
    simp [idx, targetFin, hsum]
  have hr : indexedRun c.modulus vals idx = true :=
    (indexedRun_exact c.positive vals idx).mpr hex
  have hf : indexedRun c.modulus vals idx = false := by
    simpa [idx] using c.targetAbsent
  rw [hf] at hr
  contradiction

/-- Prefer the lower predicted certificate cost; ties preserve earlier portfolio order. -/
def betterCosted {vals : List Nat} {target : Nat}
    (a b : CostedObstruction vals target) : CostedObstruction vals target :=
  if a.cost ≤ b.cost then a else b

/-- Collect every successful proof-producing residue candidate. -/
def collectCosted (vals : List Nat) (target : Nat) : List Nat → List (CostedObstruction vals target)
  | [] => []
  | m :: ms =>
      match tryCosted vals target m with
      | some c => c :: collectCosted vals target ms
      | none => collectCosted vals target ms

/-- Select the cheapest successful residue certificate rather than the first successful modulus. -/
def chooseCosted (vals : List Nat) (target : Nat) (mods : List Nat) :
    Option (CostedObstruction vals target) :=
  match collectCosted vals target mods with
  | [] => none
  | c :: cs => some (cs.foldl betterCosted c)

/-- Old first-success behavior retained only as a comparison control. -/
def chooseFirst (vals : List Nat) (target : Nat) : List Nat → Option Nat
  | [] => none
  | m :: ms =>
      match tryCosted vals target m with
      | some _ => some m
      | none => chooseFirst vals target ms

/-- Any certificate returned by the cost-aware selector transports its UNSAT proof. -/
theorem chooseCosted_sound (vals : List Nat) (target : Nat) (mods : List Nat) :
    match chooseCosted vals target mods with
    | some c => ¬ ∃ bits : List Bool,
        bits.length = vals.length ∧ selectedValue bits vals = target
    | none => True := by
  cases h : chooseCosted vals target mods with
  | none => trivial
  | some c => exact no_exact_witness_of_costed c

/-- Existing GCD branch wrapped as data so it can live in `Option`. -/
structure ExistingGCDProof (vals : List Nat) (target : Nat) : Type where
  proof : ¬ ∃ bits : List Bool,
    bits.length = vals.length ∧ selectedValue bits vals = target

/-- Abstract portfolio adapter: existing GCD proof first, new costed residue proof second,
    LRAT obligation last. The prior branches are passed through unchanged. -/
inductive PortfolioResult (vals : List Nat) (target : Nat) where
  | gcd (proof : ¬ ∃ bits : List Bool,
      bits.length = vals.length ∧ selectedValue bits vals = target)
  | residue (cert : CostedObstruction vals target)
  | lrat

/-- Semantics-preserving GCD → costed residue → LRAT adapter. -/
def choosePortfolio (vals : List Nat) (target : Nat) (mods : List Nat)
    (existingGCD : Option (ExistingGCDProof vals target)) :
    PortfolioResult vals target :=
  match existingGCD with
  | some h => .gcd h.proof
  | none =>
      match chooseCosted vals target mods with
      | some c => .residue c
      | none => .lrat

/-- Every proof-producing portfolio branch is sound; the LRAT branch remains an obligation. -/
theorem portfolio_sound (vals : List Nat) (target : Nat) (mods : List Nat)
    (existingGCD : Option (ExistingGCDProof vals target)) :
    match choosePortfolio vals target mods existingGCD with
    | .gcd h => ¬ ∃ bits : List Bool,
        bits.length = vals.length ∧ selectedValue bits vals = target
    | .residue c => ¬ ∃ bits : List Bool,
        bits.length = vals.length ∧ selectedValue bits vals = target
    | .lrat => True := by
  unfold choosePortfolio
  cases existingGCD with
  | some h => exact h.proof
  | none =>
      cases hc : chooseCosted vals target mods with
      | none => trivial
      | some c => exact no_exact_witness_of_costed c

/-- Frontier-24 decisive family: gcd 1, exact sums {0,1,5,6}, target 3 absent. -/
def decisiveVals : List Nat := [1, 5]
def decisiveTarget : Nat := 3
def frontier23Order : List Nat := [2, 3, 4, 5]

example : activeCount 4 (indexedRun 4 decisiveVals) = 3 := by decide
example : activeCount 5 (indexedRun 5 decisiveVals) = 2 := by decide
example : certificateCost 4 (indexedRun 4 decisiveVals) = 10 := by decide
example : certificateCost 5 (indexedRun 5 decisiveVals) = 9 := by decide
example : chooseFirst decisiveVals decisiveTarget frontier23Order = some 4 := by decide
example : (chooseCosted decisiveVals decisiveTarget frontier23Order).map (fun c => c.modulus) = some 5 := by decide

/-- The old order and the cost-aware selector make different choices on the same UNSAT source. -/
theorem decisive_cost_reorders_success :
    chooseFirst decisiveVals decisiveTarget frontier23Order = some 4 ∧
    (chooseCosted decisiveVals decisiveTarget frontier23Order).map (fun c => c.modulus) = some 5 := by
  decide

#print axioms indexedRun_exact
#print axioms one_transition_preserves_exact
#print axioms fullRunWork_exact
#print axioms no_exact_witness_of_costed
#print axioms chooseCosted_sound
#print axioms portfolio_sound
#print axioms decisive_cost_reorders_success

end WTCF24
