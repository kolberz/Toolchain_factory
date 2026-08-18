import OpenProblems.Complexity.DecodedInputBounds
import OpenProblems.Complexity.SAT

namespace OpenProblems.Serialization.BitCodec

open OpenProblems
open OpenProblems.Serialization

/-- A prefix-canonical codec has canonical whole-input decoding. -/
theorem decodeWhole_canonical
    (codec : BitCodec α)
    (hcanonical : PrefixCanonical codec)
    {bits : BitString}
    {value : α}
    (hdecode :
      codec.decodeWhole bits = some value) :
    bits = codec.encode value := by
  unfold BitCodec.decodeWhole at hdecode
  cases hprefix : codec.decode bits with
  | none =>
      simp [hprefix] at hdecode
  | some result =>
      rcases result with ⟨decoded, remaining⟩
      cases remaining with
      | nil =>
          simp [hprefix] at hdecode
          subst decoded
          simpa using
            hcanonical bits value [] hprefix
      | cons bit remaining =>
          simp [hprefix] at hdecode

end OpenProblems.Serialization.BitCodec

namespace OpenProblems.Complexity.CNF

open OpenProblems
open OpenProblems.Serialization
open OpenProblems.Serialization.BitCodec

/-!
# Canonical encoded-CNF witnesses and concrete SAT membership

The CNF instance and assignment codecs accept only their canonical
representations.  This makes the satisfying-assignment witness length
provably linear in the encoded instance length.
-/

theorem literalCodec_prefixCanonical :
    PrefixCanonical literalCodec := by
  intro bits literal suffix hdecode
  simp only [literalCodec] at hdecode ⊢
  cases hsign : boolCodec.decode bits with
  | none =>
      simp [hsign] at hdecode
  | some signResult =>
      rcases signResult with ⟨positive, afterSign⟩
      cases hvariable : natCodec.decode afterSign with
      | none =>
          simp [hsign, hvariable] at hdecode
      | some variableResult =>
          rcases variableResult with
            ⟨variableIndex, remaining⟩
          simp [hsign, hvariable] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          rw [boolCodec_prefixCanonical
                bits positive afterSign hsign,
              natCodec_prefixCanonical
                afterSign variableIndex remaining hvariable]
          cases positive <;>
            simp [boolCodec, natCodec]

theorem clauseCodec_prefixCanonical :
    PrefixCanonical clauseCodec :=
  listCodec_prefixCanonical
    literalCodec literalCodec_prefixCanonical

theorem formulaCodec_prefixCanonical :
    PrefixCanonical formulaCodec :=
  listCodec_prefixCanonical
    clauseCodec clauseCodec_prefixCanonical

theorem instanceCodec_prefixCanonical :
    PrefixCanonical instanceCodec := by
  intro bits inst suffix hdecode
  simp only [instanceCodec] at hdecode ⊢
  cases hvariables : natCodec.decode bits with
  | none =>
      simp [hvariables] at hdecode
  | some variableResult =>
      rcases variableResult with
        ⟨variableCount, afterVariables⟩
      cases hformula :
          formulaCodec.decode afterVariables with
      | none =>
          simp [hvariables, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with
            ⟨formula, remaining⟩
          simp [hvariables, hformula] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          rw [natCodec_prefixCanonical
                bits variableCount afterVariables hvariables,
              formulaCodec_prefixCanonical
                afterVariables formula remaining hformula]
          simp [natCodec, List.append_assoc]

theorem assignmentCodec_prefixCanonical :
    PrefixCanonical assignmentCodec :=
  listCodec_prefixCanonical
    boolCodec boolCodec_prefixCanonical

theorem decodeInstance_canonical
    {bits : BitString}
    {inst : Instance}
    (hdecode :
      decodeInstance bits = some inst) :
    bits = encodeInstance inst := by
  exact
    decodeWhole_canonical
      instanceCodec instanceCodec_prefixCanonical hdecode

theorem decodeAssignment_canonical
    {bits : BitString}
    {assignment : Assignment}
    (hdecode :
      decodeAssignment bits = some assignment) :
    bits = encodeAssignment assignment := by
  exact
    decodeWhole_canonical
      assignmentCodec assignmentCodec_prefixCanonical hdecode

@[simp]
theorem encodeAssignment_length
    (assignment : Assignment) :
    (encodeAssignment assignment).length =
      2 * assignment.length + 1 := by
  have hpayload :
      (encodeListPayload boolCodec assignment).length =
        assignment.length := by
    induction assignment with
    | nil =>
        rfl
    | cons bit remaining ih =>
        change
          ([bit] ++
            encodeListPayload boolCodec remaining).length =
              (bit :: remaining).length
        simp [ih]
  simp [encodeAssignment, assignmentCodec,
    listCodec, natCodec, encodeNat_length,
    hpayload]
  omega

theorem decoded_variableCount_succ_le_input_length
    {bits : BitString}
    {inst : Instance}
    (hdecode :
      decodeInstance bits = some inst) :
    inst.variableCount + 1 ≤ bits.length := by
  rw [decodeInstance_canonical hdecode]
  simp [encodeInstance, instanceCodec,
    natCodec, encodeNat_length]

/-- Linear witness polynomial `2n`. -/
def encodedSATWitnessPolynomial :
    NatPolynomial :=
  .mul (.constant 2) .variable

@[simp]
theorem encodedSATWitnessPolynomial_eval
    (n : Nat) :
    encodedSATWitnessPolynomial.eval n = 2 * n :=
  rfl

/-- Every satisfying encoded assignment is linearly bounded by its instance. -/
theorem encodedRelation_certificate_length_le
    {input certificate : BitString}
    (hrelation :
      EncodedRelation input certificate) :
    certificate.length ≤
      encodedSATWitnessPolynomial.eval input.length := by
  rcases hrelation with
    ⟨inst, assignment, hinput, hcertificate,
      hassignment⟩
  have hvariables :=
    decoded_variableCount_succ_le_input_length hinput
  have hcanonical :=
    congrArg List.length
      (decodeAssignment_canonical hcertificate)
  rw [encodeAssignment_length] at hcanonical
  have hlength :
      assignment.length = inst.variableCount :=
    hassignment.1
  rw [hcanonical, encodedSATWitnessPolynomial_eval,
    hlength]
  omega

/-! ## Event-instrumented verifier -/

/-- Observable bit-scan events for the encoded SAT verifier. -/
inductive EncodedSATVerifierEvent where
  | inputBit : Bool → EncodedSATVerifierEvent
  | certificateBit : Bool → EncodedSATVerifierEvent
deriving Repr, DecidableEq

structure EncodedSATVerifierResult where
  accepted : Bool
  events : List EncodedSATVerifierEvent
deriving Repr, DecidableEq

/-- The Boolean verifier and its concrete input/certificate scan trace. -/
def runEncodedSATVerifier
    (input certificate : BitString) :
    EncodedSATVerifierResult :=
  {
    accepted := encodedVerify input certificate
    events :=
      input.map EncodedSATVerifierEvent.inputBit ++
        certificate.map
          EncodedSATVerifierEvent.certificateBit
  }

@[simp]
theorem runEncodedSATVerifier_accepted
    (input certificate : BitString) :
    (runEncodedSATVerifier input certificate).accepted =
      encodedVerify input certificate :=
  rfl

@[simp]
theorem runEncodedSATVerifier_events_length
    (input certificate : BitString) :
    (runEncodedSATVerifier input certificate).events.length =
      input.length + certificate.length := by
  simp [runEncodedSATVerifier]

def operationalEncodedSATVerifier :
    PolyTimeVerifier EncodedRelation where
  verify := fun input certificate =>
    (runEncodedSATVerifier input certificate).accepted
  cost := fun input certificate =>
    (runEncodedSATVerifier input certificate).events.length
  timeBound := NatPolynomial.variable
  cost_le := by
    intro input certificate
    simp
  correct := by
    intro input certificate
    simpa using
      encodedVerify_eq_true_iff input certificate

/-- Concrete SAT witness-size certificate, closing the prior open interface. -/
def encodedSatisfiableWitnessSizeCertificate :
    SATWitnessSizeCertificate where
  bound := encodedSATWitnessPolynomial
  bounded := by
    intro input certificate hrelation
    exact encodedRelation_certificate_length_le hrelation

/--
Encoded SAT with an event-instrumented polynomial verifier and an explicit
linear witness bound.
-/
def encodedSatisfiablePolynomialWitnessSystem :
    PolynomialWitnessSystem EncodedSatisfiable where
  relation := EncodedRelation
  verifier := operationalEncodedSATVerifier
  witnessSizeBound := encodedSATWitnessPolynomial
  sound_complete := by
    intro input
    constructor
    · rintro ⟨certificate, hrelation⟩
      exact
        ⟨certificate,
          encodedRelation_certificate_length_le hrelation,
          hrelation⟩
    · rintro ⟨certificate, _, hrelation⟩
      exact ⟨certificate, hrelation⟩

theorem encodedSatisfiable_iff_bounded_verified
    (input : BitString) :
    EncodedSatisfiable input ↔
      ∃ certificate,
        certificate.length ≤
          encodedSATWitnessPolynomial.eval input.length ∧
        operationalEncodedSATVerifier.verify
          input certificate = true := by
  constructor
  · intro hsat
    exact
      PolynomialWitnessSystem.exists_verified_certificate
        encodedSatisfiablePolynomialWitnessSystem hsat
  · rintro ⟨certificate, hsize, hverify⟩
    exact
      PolynomialWitnessSystem.member_of_verified
        encodedSatisfiablePolynomialWitnessSystem
        hsize hverify

end OpenProblems.Complexity.CNF
