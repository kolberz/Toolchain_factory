import OpenProblems.Complexity.EncodedSATMembership

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Serialization
open OpenProblems.Serialization.BitCodec

namespace CNF

/-!
# Physical codec layouts for a prefix-SAT tape machine

The declarations below contain no machine table.  They expose the exact bit
blocks hidden by the compositional codecs:

* naturals are unary `true` blocks with one `false` terminator;
* every list starts with such a unary length block;
* literals contain one polarity bit followed by a unary variable index;
* a CNF instance is a whole-input value; and
* an assignment is only a certificate prefix, so its unused suffix is retained.

The successful-decoder lemmas turn semantic decoder hypotheses into literal
equalities of physical bit strings.  They are intended as rewrite boundaries
for later tape-configuration and machine-run proofs.
-/

/-! ## Primitive physical blocks -/

/-- Unary naturals are a block of `true` markers and one `false` terminator. -/
@[simp]
theorem encodeNat_physical_layout
    (value : Nat) :
    encodeNat value =
      List.replicate value true ++ [false] := by
  induction value with
  | zero =>
      rfl
  | succ value ih =>
      simp [encodeNat, ih, List.replicate_succ]

/-- Encoding a Boolean list payload contributes exactly its raw Boolean bits. -/
@[simp]
theorem encodeListPayload_boolCodec_layout
    (values : List Bool) :
    encodeListPayload boolCodec values = values := by
  induction values with
  | nil =>
      rfl
  | cons value values ih =>
      change
        [value] ++ encodeListPayload boolCodec values =
          value :: values
      simp [ih]

/-- Positive literal block: positive tag, unary index, terminator. -/
@[simp]
theorem literalCodec_encode_positive_layout
    (index : Nat) :
    literalCodec.encode (.positive index) =
      true :: List.replicate index true ++ [false] := by
  simp [literalCodec, boolCodec, natCodec,
    encodeNat_physical_layout]

/-- Negative literal block: negative tag, unary index, terminator. -/
@[simp]
theorem literalCodec_encode_negative_layout
    (index : Nat) :
    literalCodec.encode (.negative index) =
      false :: List.replicate index true ++ [false] := by
  simp [literalCodec, boolCodec, natCodec,
    encodeNat_physical_layout]

/-! ## Nested list and top-level layouts -/

/-- A clause starts with its unary literal count and then its literal payload. -/
@[simp]
theorem clauseCodec_encode_physical_layout
    (clause : Clause) :
    clauseCodec.encode clause =
      List.replicate clause.length true ++
        false :: encodeListPayload literalCodec clause := by
  simp [clauseCodec, listCodec, natCodec,
    encodeNat_physical_layout, List.append_assoc]

/-- A formula starts with its unary clause count and then its clause payload. -/
@[simp]
theorem formulaCodec_encode_physical_layout
    (formula : Formula) :
    formulaCodec.encode formula =
      List.replicate formula.length true ++
        false :: encodeListPayload clauseCodec formula := by
  simp [formulaCodec, listCodec, natCodec,
    encodeNat_physical_layout, List.append_assoc]

/-- An assignment prefix is unary length, terminator, then the raw value bits. -/
@[simp]
theorem assignmentCodec_encode_physical_layout
    (assignment : Assignment) :
    assignmentCodec.encode assignment =
      List.replicate assignment.length true ++
        false :: assignment := by
  simp [assignmentCodec, listCodec, natCodec,
    encodeNat_physical_layout,
    encodeListPayload_boolCodec_layout,
    List.append_assoc]

/-- Exact wrapper-level assignment layout. -/
@[simp]
theorem encodeAssignment_physical_layout
    (assignment : Assignment) :
    encodeAssignment assignment =
      List.replicate assignment.length true ++
        false :: assignment := by
  simp [encodeAssignment]

/--
An instance is the unary variable count followed by the unary clause count and
the recursively encoded clause payload.
-/
@[simp]
theorem encodeInstance_physical_layout
    (inst : Instance) :
    encodeInstance inst =
      List.replicate inst.variableCount true ++
        false ::
          (List.replicate inst.formula.length true ++
            false :: encodeListPayload clauseCodec inst.formula) := by
  simp [encodeInstance, instanceCodec, natCodec,
    encodeNat_physical_layout,
    formulaCodec_encode_physical_layout,
    List.append_assoc]

/-! ## Exact decoder behavior on encoded prefixes -/

/-- A codec prefix decoder returns an arbitrary appended suffix unchanged. -/
theorem decodeWholeCodecPrefix_encode_append
    (codec : BitCodec α)
    (value : α)
    (suffix : BitString) :
    codec.decode (codec.encode value ++ suffix) =
      some (value, suffix) :=
  codec.decode_encode value suffix

/--
Whole-input decoding of an encoded value succeeds exactly when the appended
suffix is empty.
-/
theorem decodeWhole_encode_append
    (codec : BitCodec α)
    (value : α)
    (suffix : BitString) :
    codec.decodeWhole (codec.encode value ++ suffix) =
      match suffix with
      | [] => some value
      | _ :: _ => none := by
  unfold BitCodec.decodeWhole
  rw [codec.decode_encode]
  cases suffix <;> rfl

@[simp]
theorem instanceCodec_decode_encodeInstance_append
    (inst : Instance)
    (suffix : BitString) :
    instanceCodec.decode (encodeInstance inst ++ suffix) =
      some (inst, suffix) := by
  exact instanceCodec.decode_encode inst suffix

@[simp]
theorem assignmentCodec_decode_encodeAssignment_append
    (assignment : Assignment)
    (suffix : BitString) :
    assignmentCodec.decode
        (encodeAssignment assignment ++ suffix) =
      some (assignment, suffix) := by
  simpa [encodeAssignment] using
    assignmentCodec.decode_encode assignment suffix

theorem decodeInstance_encode_append
    (inst : Instance)
    (suffix : BitString) :
    decodeInstance (encodeInstance inst ++ suffix) =
      match suffix with
      | [] => some inst
      | _ :: _ => none := by
  simpa [decodeInstance, encodeInstance] using
    decodeWhole_encode_append instanceCodec inst suffix

theorem decodeAssignment_encode_append
    (assignment : Assignment)
    (suffix : BitString) :
    decodeAssignment (encodeAssignment assignment ++ suffix) =
      match suffix with
      | [] => some assignment
      | _ :: _ => none := by
  simpa [decodeAssignment, encodeAssignment] using
    decodeWhole_encode_append assignmentCodec assignment suffix

@[simp]
theorem decodeInstance_encode_append_cons
    (inst : Instance)
    (bit : Bool)
    (suffix : BitString) :
    decodeInstance
        (encodeInstance inst ++ bit :: suffix) =
      none := by
  simpa using
    decodeInstance_encode_append inst (bit :: suffix)

@[simp]
theorem decodeAssignment_encode_append_cons
    (assignment : Assignment)
    (bit : Bool)
    (suffix : BitString) :
    decodeAssignment
        (encodeAssignment assignment ++ bit :: suffix) =
      none := by
  simpa using
    decodeAssignment_encode_append
      assignment (bit :: suffix)

/-! ## Whole-input versus prefix decoder boundaries -/

/-- `decodeInstance` is the instance prefix decoder plus an empty-suffix test. -/
theorem decodeInstance_eq_some_iff_prefix_empty
    (bits : BitString)
    (inst : Instance) :
    decodeInstance bits = some inst ↔
      instanceCodec.decode bits = some (inst, []) := by
  unfold decodeInstance BitCodec.decodeWhole
  cases hdecode : instanceCodec.decode bits with
  | none =>
      simp
  | some result =>
      rcases result with ⟨decoded, suffix⟩
      cases suffix <;> simp

/--
`decodeAssignment` is the whole-input variant of the assignment prefix decoder.
The prefix-SAT verifier intentionally uses the right-hand decoder directly.
-/
theorem decodeAssignment_eq_some_iff_prefix_empty
    (bits : BitString)
    (assignment : Assignment) :
    decodeAssignment bits = some assignment ↔
      assignmentCodec.decode bits =
        some (assignment, []) := by
  unfold decodeAssignment BitCodec.decodeWhole
  cases hdecode : assignmentCodec.decode bits with
  | none =>
      simp
  | some result =>
      rcases result with ⟨decoded, suffix⟩
      cases suffix <;> simp

/-! ## Successful decoder phase decompositions -/

/--
Successful instance-prefix decoding is exactly a unary variable-count decode
followed by a formula decode.  The returned formula suffix is the returned
instance suffix.
-/
theorem instanceCodec_decode_eq_some_iff_phases
    (bits : BitString)
    (inst : Instance)
    (suffix : BitString) :
    instanceCodec.decode bits = some (inst, suffix) ↔
      ∃ formulaBits,
        natCodec.decode bits =
            some (inst.variableCount, formulaBits) ∧
          formulaCodec.decode formulaBits =
            some (inst.formula, suffix) := by
  cases inst with
  | mk variableCount formula =>
      constructor
      · intro hdecode
        cases hvariables : natCodec.decode bits with
        | none =>
            simp [instanceCodec, hvariables] at hdecode
        | some variableResult =>
            rcases variableResult with
              ⟨decodedVariableCount, formulaBits⟩
            cases hformula :
                formulaCodec.decode formulaBits with
            | none =>
                simp [instanceCodec, hvariables,
                  hformula] at hdecode
            | some formulaResult =>
                rcases formulaResult with
                  ⟨decodedFormula, remaining⟩
                have heq :
                    (decodedVariableCount = variableCount ∧
                        decodedFormula = formula) ∧
                      remaining = suffix := by
                  simpa [instanceCodec, hvariables,
                    hformula] using hdecode
                rcases heq with
                  ⟨⟨rfl, rfl⟩, rfl⟩
                exact
                  ⟨formulaBits, rfl, hformula⟩
      · rintro ⟨formulaBits, hvariables, hformula⟩
        simp [instanceCodec, hvariables, hformula]

/--
Successful assignment-prefix decoding is exactly a unary payload-count decode
followed by `decodeListN` over raw Boolean cells.
-/
theorem assignmentCodec_decode_eq_some_iff_phases
    (bits : BitString)
    (assignment : Assignment)
    (suffix : BitString) :
    assignmentCodec.decode bits =
        some (assignment, suffix) ↔
      ∃ count payloadBits,
        natCodec.decode bits = some (count, payloadBits) ∧
          decodeListN boolCodec count payloadBits =
            some (assignment, suffix) := by
  constructor
  · intro hdecode
    cases hcount : natCodec.decode bits with
    | none =>
        simp [assignmentCodec, listCodec,
          hcount] at hdecode
    | some countResult =>
        rcases countResult with ⟨count, payloadBits⟩
        cases hpayload :
            decodeListN boolCodec count payloadBits with
        | none =>
            simp [assignmentCodec, listCodec,
              hcount, hpayload] at hdecode
        | some payloadResult =>
            rcases payloadResult with
              ⟨decodedAssignment, remaining⟩
            have heq :
                decodedAssignment = assignment ∧
                  remaining = suffix := by
              simpa [assignmentCodec, listCodec,
                hcount, hpayload] using hdecode
            rcases heq with ⟨rfl, rfl⟩
            exact
              ⟨count, payloadBits, rfl, hpayload⟩
  · rintro ⟨count, payloadBits, hcount, hpayload⟩
    simp [assignmentCodec, listCodec,
      hcount, hpayload]

/--
The assignment count returned by a successful phase decomposition is the
length of the decoded assignment.
-/
theorem assignmentCodec_decode_eq_some_iff_length_phases
    (bits : BitString)
    (assignment : Assignment)
    (suffix : BitString) :
    assignmentCodec.decode bits =
        some (assignment, suffix) ↔
      ∃ payloadBits,
        natCodec.decode bits =
            some (assignment.length, payloadBits) ∧
          decodeListN boolCodec assignment.length payloadBits =
            some (assignment, suffix) := by
  constructor
  · intro hdecode
    rcases
        (assignmentCodec_decode_eq_some_iff_phases
          bits assignment suffix).mp hdecode with
      ⟨count, payloadBits, hcount, hpayload⟩
    have hlength :
        assignment.length = count :=
      (decodeListN_prefix
        boolCodec boolCodec_prefixCanonical hpayload).1
    subst count
    exact ⟨payloadBits, hcount, hpayload⟩
  · rintro ⟨payloadBits, hcount, hpayload⟩
    exact
      (assignmentCodec_decode_eq_some_iff_phases
        bits assignment suffix).mpr
          ⟨assignment.length, payloadBits,
            hcount, hpayload⟩

/-- Whole-instance success is the empty-suffix instance phase decomposition. -/
theorem decodeInstance_eq_some_iff_phases
    (bits : BitString)
    (inst : Instance) :
    decodeInstance bits = some inst ↔
      ∃ formulaBits,
        natCodec.decode bits =
            some (inst.variableCount, formulaBits) ∧
          formulaCodec.decode formulaBits =
            some (inst.formula, []) := by
  rw [decodeInstance_eq_some_iff_prefix_empty]
  exact
    instanceCodec_decode_eq_some_iff_phases
      bits inst []

/-- Whole-assignment success is the empty-suffix assignment decomposition. -/
theorem decodeAssignment_eq_some_iff_phases
    (bits : BitString)
    (assignment : Assignment) :
    decodeAssignment bits = some assignment ↔
      ∃ payloadBits,
        natCodec.decode bits =
            some (assignment.length, payloadBits) ∧
          decodeListN boolCodec assignment.length payloadBits =
            some (assignment, []) := by
  rw [decodeAssignment_eq_some_iff_prefix_empty]
  exact
    assignmentCodec_decode_eq_some_iff_length_phases
      bits assignment []

/-! ## Canonical decompositions from successful decoders -/

theorem literalCodec_decode_success
    {bits : BitString}
    {literal : Literal}
    {suffix : BitString}
    (hdecode :
      literalCodec.decode bits =
        some (literal, suffix)) :
    bits = literalCodec.encode literal ++ suffix :=
  literalCodec_prefixCanonical
    bits literal suffix hdecode

theorem literalCodec_decode_positive_physical_layout
    {bits suffix : BitString}
    {index : Nat}
    (hdecode :
      literalCodec.decode bits =
        some (.positive index, suffix)) :
    bits =
      (true :: List.replicate index true ++ [false]) ++
        suffix := by
  rw [literalCodec_decode_success hdecode]
  rw [literalCodec_encode_positive_layout]

theorem literalCodec_decode_negative_physical_layout
    {bits suffix : BitString}
    {index : Nat}
    (hdecode :
      literalCodec.decode bits =
        some (.negative index, suffix)) :
    bits =
      (false :: List.replicate index true ++ [false]) ++
        suffix := by
  rw [literalCodec_decode_success hdecode]
  rw [literalCodec_encode_negative_layout]

theorem clauseCodec_decode_physical_layout
    {bits suffix : BitString}
    {clause : Clause}
    (hdecode :
      clauseCodec.decode bits =
        some (clause, suffix)) :
    bits =
      (List.replicate clause.length true ++
        false :: encodeListPayload literalCodec clause) ++
          suffix := by
  rw [clauseCodec_prefixCanonical
    bits clause suffix hdecode]
  rw [clauseCodec_encode_physical_layout]

theorem formulaCodec_decode_physical_layout
    {bits suffix : BitString}
    {formula : Formula}
    (hdecode :
      formulaCodec.decode bits =
        some (formula, suffix)) :
    bits =
      (List.replicate formula.length true ++
        false :: encodeListPayload clauseCodec formula) ++
          suffix := by
  rw [formulaCodec_prefixCanonical
    bits formula suffix hdecode]
  rw [formulaCodec_encode_physical_layout]

/-- Successful instance prefix decoding retains its arbitrary trailing suffix. -/
theorem instanceCodec_decode_physical_layout
    {bits suffix : BitString}
    {inst : Instance}
    (hdecode :
      instanceCodec.decode bits =
        some (inst, suffix)) :
    bits =
      (List.replicate inst.variableCount true ++
        false ::
          (List.replicate inst.formula.length true ++
            false ::
              encodeListPayload clauseCodec inst.formula)) ++
        suffix := by
  rw [instanceCodec_prefixCanonical
    bits inst suffix hdecode]
  change
    encodeInstance inst ++ suffix =
      (List.replicate inst.variableCount true ++
        false ::
          (List.replicate inst.formula.length true ++
            false ::
              encodeListPayload clauseCodec inst.formula)) ++
        suffix
  rw [encodeInstance_physical_layout]

/-- Successful whole-instance decoding has no trailing input tape. -/
theorem decodeInstance_physical_layout
    {bits : BitString}
    {inst : Instance}
    (hdecode :
      decodeInstance bits = some inst) :
    bits =
      List.replicate inst.variableCount true ++
        false ::
          (List.replicate inst.formula.length true ++
            false ::
              encodeListPayload clauseCodec inst.formula) := by
  rw [decodeInstance_canonical hdecode]
  exact encodeInstance_physical_layout inst

/--
Successful assignment-prefix decoding exposes unary length, raw assignment
bits, and the untouched certificate suffix.
-/
theorem assignmentCodec_decode_physical_layout
    {bits suffix : BitString}
    {assignment : Assignment}
    (hdecode :
      assignmentCodec.decode bits =
        some (assignment, suffix)) :
    bits =
      (List.replicate assignment.length true ++
        false :: assignment) ++ suffix := by
  rw [assignmentCodec_prefixCanonical
    bits assignment suffix hdecode]
  rw [assignmentCodec_encode_physical_layout]

/-- Successful whole-assignment decoding is the empty-suffix specialization. -/
theorem decodeAssignment_physical_layout
    {bits : BitString}
    {assignment : Assignment}
    (hdecode :
      decodeAssignment bits = some assignment) :
    bits =
      List.replicate assignment.length true ++
        false :: assignment := by
  rw [decodeAssignment_canonical hdecode]
  exact encodeAssignment_physical_layout assignment

/-! ## Payload decompositions used inside the list codecs -/

/--
A successful Boolean payload decode consumes exactly `count` raw bits and
leaves its suffix untouched.
-/
theorem decodeListN_boolCodec_physical_layout
    {count : Nat}
    {bits suffix : BitString}
    {values : List Bool}
    (hdecode :
      decodeListN boolCodec count bits =
        some (values, suffix)) :
    values.length = count ∧
      bits = values ++ suffix := by
  rcases
      decodeListN_prefix
        boolCodec boolCodec_prefixCanonical hdecode with
    ⟨hlength, hbits⟩
  exact
    ⟨hlength,
      by simpa using hbits⟩

/-- A successful literal payload decode consumes exactly the declared count. -/
theorem decodeListN_literalCodec_physical_layout
    {count : Nat}
    {bits suffix : BitString}
    {literals : List Literal}
    (hdecode :
      decodeListN literalCodec count bits =
        some (literals, suffix)) :
    literals.length = count ∧
      bits =
        encodeListPayload literalCodec literals ++ suffix :=
  decodeListN_prefix
    literalCodec literalCodec_prefixCanonical hdecode

/-- A successful clause payload decode consumes exactly the declared count. -/
theorem decodeListN_clauseCodec_physical_layout
    {count : Nat}
    {bits suffix : BitString}
    {clauses : List Clause}
    (hdecode :
      decodeListN clauseCodec count bits =
        some (clauses, suffix)) :
    clauses.length = count ∧
      bits =
        encodeListPayload clauseCodec clauses ++ suffix :=
  decodeListN_prefix
    clauseCodec clauseCodec_prefixCanonical hdecode

end CNF

end OpenProblems.Complexity
