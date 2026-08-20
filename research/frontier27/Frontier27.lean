import Frontier26

namespace WTCF27
open WTC
open WTCF21
open WTCF22
open WTCF23
open WTCF25
open WTCF26

abbrev Byte := Fin 256

def byteOfNat (n : Nat) : Byte :=
  ⟨n % 256, Nat.mod_lt _ (by decide)⟩

def natOfByte (b : Byte) : Nat := b.val

def serializeWords (xs : List Nat) : List Byte := xs.map byteOfNat

def deserializeWords (bs : List Byte) : List Nat := bs.map natOfByte

@[simp] theorem serializeWords_length (xs : List Nat) :
    (serializeWords xs).length = xs.length := by
  simp [serializeWords]

theorem deserialize_serialize_bounded (xs : List Nat)
    (hbound : ∀ n ∈ xs, n < 256) :
    deserializeWords (serializeWords xs) = xs := by
  induction xs with
  | nil => simp [serializeWords, deserializeWords]
  | cons x xs ih =>
      have hx : x < 256 := hbound x (by simp)
      have hxs : ∀ n ∈ xs, n < 256 := by
        intro n hn
        exact hbound n (by simp [hn])
      change natOfByte (byteOfNat x) :: deserializeWords (serializeWords xs) = x :: xs
      have hxbyte : natOfByte (byteOfNat x) = x := by
        simp [natOfByte, byteOfNat, Nat.mod_eq_of_lt hx]
      rw [hxbyte, ih hxs]

private theorem bitmapWords_bounded (m : Nat) (s : WTCF25.ResidueState m) :
    ∀ n ∈ WTCF26.bitmapWords m s, n < 256 := by
  intro n hn
  rcases List.mem_map.mp hn with ⟨r, hr, rfl⟩
  cases h : s r <;> simp [WTCF26.bitmapWords, h]

private theorem activePayload_bounded {m : Nat} (hm : m ≤ 256)
    (rs : List (Fin m)) :
    ∀ n ∈ WTCF26.activePayload rs, n < 256 := by
  induction rs with
  | nil => simp [WTCF26.activePayload]
  | cons r rs ih =>
      intro n hn
      simp only [WTCF26.activePayload, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact Nat.lt_of_lt_of_le r.isLt hm
      · rcases hn with rfl | hn
        · decide
        · exact ih n hn

theorem emittedEvidence_bounded (m : Nat) (s : WTCF25.ResidueState m)
    (hm : m ≤ 256) :
    ∀ n ∈ WTCF26.emitResidueEvidence m s, n < 256 := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · exact bitmapWords_bounded m s n hn
  · exact activePayload_bounded hm (WTCF26.activeIndices m s) n hn

def serializeEvidence (m : Nat) (s : WTCF25.ResidueState m) : List Byte :=
  serializeWords (WTCF26.emitResidueEvidence m s)

def serializedEvidenceBytes (m : Nat) (s : WTCF25.ResidueState m) : Nat :=
  (serializeEvidence m s).length

theorem serializedEvidenceBytes_eq_words (m : Nat) (s : WTCF25.ResidueState m) :
    serializedEvidenceBytes m s = WTCF26.emittedEvidenceWords m s := by
  simp [serializedEvidenceBytes, serializeEvidence, WTCF26.emittedEvidenceWords]

theorem deserialize_serializeEvidence (m : Nat) (s : WTCF25.ResidueState m)
    (hm : m ≤ 256) :
    deserializeWords (serializeEvidence m s) = WTCF26.emitResidueEvidence m s := by
  apply deserialize_serialize_bounded
  exact emittedEvidence_bounded m s hm

def certificateBytes {I : SubsetSumFW} (c : WTCF25.CostedWTCObstruction I) : Nat :=
  serializedEvidenceBytes c.modulus
    (WTCF25.linearRun c.modulus c.positive (I.values.map wordValue))

theorem certificateBytes_eq_cost {I : SubsetSumFW}
    (c : WTCF25.CostedWTCObstruction I) :
    certificateBytes c = c.cost := by
  calc
    certificateBytes c = WTCF26.certificateWords c := by
      simp [certificateBytes, serializedEvidenceBytes_eq_words,
        WTCF26.certificateWords, WTCF26.certificateEvidence,
        WTCF26.emittedEvidenceWords]
    _ = c.cost := (WTCF26.cost_eq_certificateWords c).symm

theorem certificateBytes_ge_modulus {I : SubsetSumFW}
    (c : WTCF25.CostedWTCObstruction I) :
    c.modulus ≤ certificateBytes c := by
  rw [certificateBytes_eq_cost, c.cost_eq]
  simp [WTCF24.certificateCost]

theorem tryCosted_modulus {I : SubsetSumFW} {m : Nat}
    {c : WTCF25.CostedWTCObstruction I}
    (h : WTCF25.tryCosted I m = some c) : c.modulus = m := by
  unfold WTCF25.tryCosted at h
  split at h <;> simp_all
  rcases h with ⟨ht, hEq⟩
  exact (congrArg (fun x : WTCF25.CostedWTCObstruction I => x.modulus) hEq).symm

theorem safe_prune_tryCosted {I : SubsetSumFW} {m : Nat}
    (best c : WTCF25.CostedWTCObstruction I)
    (hbound : certificateBytes best ≤ m)
    (hc : WTCF25.tryCosted I m = some c) :
    certificateBytes best ≤ certificateBytes c := by
  have hm : c.modulus = m := tryCosted_modulus hc
  exact Nat.le_trans hbound (by simpa [hm] using certificateBytes_ge_modulus c)

def betterBytes {I : SubsetSumFW}
    (a b : WTCF25.CostedWTCObstruction I) : WTCF25.CostedWTCObstruction I :=
  if certificateBytes a ≤ certificateBytes b then a else b

structure BBTrace (I : SubsetSumFW) where
  best : WTCF25.CostedWTCObstruction I
  materialized : List Nat
  pruned : List Nat

def branchBoundFrom {I : SubsetSumFW}
    (best : WTCF25.CostedWTCObstruction I) : List Nat → BBTrace I
  | [] => { best := best, materialized := [], pruned := [] }
  | m :: ms =>
      if certificateBytes best ≤ m then
        let r := branchBoundFrom best ms
        { best := r.best, materialized := r.materialized, pruned := m :: r.pruned }
      else
        match WTCF25.tryCosted I m with
        | none =>
            let r := branchBoundFrom best ms
            { best := r.best, materialized := m :: r.materialized, pruned := r.pruned }
        | some c =>
            let r := branchBoundFrom (betterBytes best c) ms
            { best := r.best, materialized := m :: r.materialized, pruned := r.pruned }

theorem branchBoundFrom_sound {I : SubsetSumFW}
    (best : WTCF25.CostedWTCObstruction I) (mods : List Nat) :
    ¬ ∃ base : Assignment, naturalSubsetAccepts I base :=
  WTCF25.no_source_witness_of_costed (branchBoundFrom best mods).best

abbrev pruneDemo : SubsetSumFW := WTCF26.calibrationDemo
abbrev pruneSeedMods : List Nat := [2, 3, 4, 5]
abbrev pruneTailMods : List Nat := [20, 32, 64]
abbrev pruneAllMods : List Nat := pruneSeedMods ++ pruneTailMods

def pruneSeedBest : WTCF25.CostedWTCObstruction pruneDemo := by
  have h : (WTCF25.chooseCosted pruneDemo pruneSeedMods).isSome = true := by decide
  exact (WTCF25.chooseCosted pruneDemo pruneSeedMods).get
    (by simpa [Option.isSome_iff_ne_none] using h)

abbrev pruneTrace : BBTrace pruneDemo := branchBoundFrom pruneSeedBest pruneTailMods

theorem pruneAllMods_bounded : ∀ m ∈ pruneAllMods, m ≤ 256 := by
  decide

theorem pruneSeedBest_exact :
    (pruneSeedBest.modulus, certificateBytes pruneSeedBest) = (5, 9) := by
  decide

theorem pruneTrace_exact :
    pruneTrace.materialized = [] ∧
    pruneTrace.pruned = [20, 32, 64] ∧
    (pruneTrace.best.modulus, certificateBytes pruneTrace.best) = (5, 9) := by
  decide

theorem exhaustive_byte_min_exact :
    (WTCF25.chooseCosted pruneDemo pruneAllMods).map
      (fun c => (c.modulus, certificateBytes c)) = some (5, 9) := by
  decide

theorem branch_bound_exhaustive_equiv :
    some (pruneTrace.best.modulus, certificateBytes pruneTrace.best) =
      (WTCF25.chooseCosted pruneDemo pruneAllMods).map
        (fun c => (c.modulus, certificateBytes c)) := by
  decide

def branchBoundMaterializationWork (I : SubsetSumFW) (seedMods : List Nat)
    (trace : BBTrace I) : Nat :=
  WTCF26.portfolioMaterializationWork I seedMods +
    WTCF26.portfolioMaterializationWork I trace.materialized

theorem pruneDemo_saved_work_exact :
    WTCF26.portfolioMaterializationWork pruneDemo pruneAllMods = 260 ∧
    branchBoundMaterializationWork pruneDemo pruneSeedMods pruneTrace = 28 ∧
    WTCF26.portfolioMaterializationWork pruneDemo pruneAllMods -
      branchBoundMaterializationWork pruneDemo pruneSeedMods pruneTrace = 232 := by
  decide

def chooseBytePortfolio (I : SubsetSumFW) : WTCF25.PortfolioResult I :=
  match WTCF22.tryGCD I with
  | some c => .gcd c
  | none =>
      match WTCF25.chooseCosted I WTCF23.residuePortfolioModuli with
      | some c => .residue c
      | none => .lrat

theorem bytePortfolio_certificate_sound (I : SubsetSumFW) :
    match chooseBytePortfolio I with
    | .gcd _ => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .residue _ => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .lrat => True := by
  unfold chooseBytePortfolio
  cases hg : WTCF22.tryGCD I with
  | some c => exact WTCF21.no_source_witness_of_mod c
  | none =>
      cases hc : WTCF25.chooseCosted I WTCF23.residuePortfolioModuli with
      | none => trivial
      | some c => exact WTCF25.no_source_witness_of_costed c

example : WTCF25.PortfolioResult.tag (chooseBytePortfolio WTCF22.nonPow2Demo) = .gcd 6 := by decide
example : WTCF26.isResidue (chooseBytePortfolio WTCF23.residueUpgrade) = true := by decide
example : WTCF26.isLRAT (chooseBytePortfolio WTCF23.residueFallback) = true := by decide

theorem residueUpgrade_target_unsat_retained :
    ¬ ∃ a, SatCNF a
      (compileProgram (compileClosedSubset WTCF23.residueUpgrade).insts
        (compileClosedSubset WTCF23.residueUpgrade).output) :=
  WTCF26.residueUpgrade_target_unsat_retained

theorem residueFallback_target_unsat_retained :
    ¬ ∃ a, SatCNF a WTCF23.residueFallbackTarget :=
  WTCF26.residueFallback_target_unsat_retained

#print axioms deserialize_serialize_bounded
#print axioms emittedEvidence_bounded
#print axioms deserialize_serializeEvidence
#print axioms certificateBytes_eq_cost
#print axioms certificateBytes_ge_modulus
#print axioms safe_prune_tryCosted
#print axioms branchBoundFrom_sound
#print axioms pruneTrace_exact
#print axioms exhaustive_byte_min_exact
#print axioms branch_bound_exhaustive_equiv
#print axioms pruneDemo_saved_work_exact
#print axioms bytePortfolio_certificate_sound
#print axioms residueUpgrade_target_unsat_retained
#print axioms residueFallback_target_unsat_retained

end WTCF27
