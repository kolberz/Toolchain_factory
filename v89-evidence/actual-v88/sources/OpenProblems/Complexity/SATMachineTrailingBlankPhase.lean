import OpenProblems.Complexity.SATMachineDefaultLookupPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

/-- Materialize one redundant blank at the far right of the finite tape zipper. -/
def appendTrailingBlank
    (blank : Symbol)
    (config : Config State Symbol) : Config State Symbol :=
  { config with tape := { config.tape with right := config.tape.right ++ [blank] } }

/-- Two configurations differ by at most one redundant far-right blank. -/
def trailingBlankRel
    (blank : Symbol)
    (canonical materialized : Config State Symbol) : Prop :=
  materialized = canonical ∨ materialized = appendTrailingBlank blank canonical

@[simp]
theorem appendTrailingBlank_state
    (blank : Symbol)
    (config : Config State Symbol) :
    (appendTrailingBlank blank config).state = config.state :=
  rfl

/-- One redundant trailing blank is preserved by one control-machine step,
or disappears exactly when the head crosses the represented right boundary. -/
theorem trailingBlankRel_step
    (machine : ControlMachine State Symbol)
    (canonical materialized : Config State Symbol)
    (hrel : trailingBlankRel machine.blank canonical materialized) :
    trailingBlankRel machine.blank
      (machine.stepConfig canonical)
      (machine.stepConfig materialized) := by
  rcases hrel with rfl | rfl
  · exact Or.inl rfl
  · cases canonical with
    | mk state tape =>
        cases tape with
        | mk left head right =>
            unfold trailingBlankRel appendTrailingBlank
            unfold ControlMachine.stepConfig
            by_cases hhalt : machine.halt state = true
            · simp [hhalt]
            · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
              generalize machine.transition state head = action
              cases action with
              | mk next write move =>
                  cases move with
                  | stay =>
                      exact Or.inr rfl
                  | left =>
                      cases left <;> simp [Tape.write, Tape.moveLeft]
                  | right =>
                      cases right with
                      | nil =>
                          exact Or.inl (by simp [Tape.write, Tape.moveRight])
                      | cons first rest =>
                          exact Or.inr (by
                            simp [Tape.write, Tape.moveRight])

/-- The one-blank relation is preserved for every bounded run. -/
theorem trailingBlankRel_run
    (machine : ControlMachine State Symbol)
    (steps : Nat)
    (canonical materialized : Config State Symbol)
    (hrel : trailingBlankRel machine.blank canonical materialized) :
    trailingBlankRel machine.blank
      (machine.run steps canonical)
      (machine.run steps materialized) := by
  induction steps generalizing canonical materialized with
  | zero =>
      simpa using hrel
  | succ steps ih =>
      rw [ControlMachine.run_succ, ControlMachine.run_succ]
      exact ih _ _ (trailingBlankRel_step machine canonical materialized hrel)

/-- Related runs always have exactly the same control state. -/
theorem trailingBlankRel_run_state
    (machine : ControlMachine State Symbol)
    (steps : Nat)
    (canonical materialized : Config State Symbol)
    (hrel : trailingBlankRel machine.blank canonical materialized) :
    (machine.run steps canonical).state =
      (machine.run steps materialized).state := by
  have hrun := trailingBlankRel_run machine steps canonical materialized hrel
  rcases hrun with h | h
  · rw [h]
  · rw [h]
    rfl


open SATMachineSymbol SATMachineState SATMachineControl

/-- Canonical logical result of a default-false lookup, with no redundant
far-right blank materialized when the logical suffix is empty. -/
def canonicalDefaultLiteralEvaluatedConfig
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || applyPolarity positive false)) blank
    (clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate (visited.length + extraIndex + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentSymbol ++
            suffix.map ofBool)

/-- The exact default-lookup output differs from its canonical logical tape by
at most the single redundant far-right blank introduced at an implicit edge. -/
theorem canonical_defaultLiteral_trailingBlankRel
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (canonicalDefaultLiteralEvaluatedConfig formulaValue clauseValue positive
        variableCount remainingClauses remainingLiterals visited extraIndex
        restLiteralPayload restPayload suffix)
      (defaultLiteralEvaluatedConfig formulaValue clauseValue positive
        variableCount remainingClauses remainingLiterals visited extraIndex
        restLiteralPayload restPayload suffix) := by
  cases suffix with
  | nil =>
      exact Or.inr (by
        simp [defaultLiteralEvaluatedConfig,
          canonicalDefaultLiteralEvaluatedConfig, appendTrailingBlank,
          configAt, tapeAt, defaultSuffixSymbols, List.append_assoc])
  | cons bit rest =>
      exact Or.inl rfl

/-- Any continuation from a canonical default-lookup result and the actual
materialized result has exactly the same control state. -/
theorem run_canonical_defaultLiteral_state
    (steps : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString) :
    (satControl.run steps
      (canonicalDefaultLiteralEvaluatedConfig formulaValue clauseValue positive
        variableCount remainingClauses remainingLiterals visited extraIndex
        restLiteralPayload restPayload suffix)).state =
    (satControl.run steps
      (defaultLiteralEvaluatedConfig formulaValue clauseValue positive
        variableCount remainingClauses remainingLiterals visited extraIndex
        restLiteralPayload restPayload suffix)).state := by
  exact trailingBlankRel_run_state satControl steps _ _
    (canonical_defaultLiteral_trailingBlankRel formulaValue clauseValue positive
      variableCount remainingClauses remainingLiterals visited extraIndex
      restLiteralPayload restPayload suffix)


/-- One canonical logical post-state for a fully evaluated CNF literal.  It
uses the literal's real index, restores the complete assignment, and omits any
redundant materialized far-right blank. -/
def canonicalCNFLiteralEvaluatedConfig
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal)) blank
    (clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate (cnfLiteralIndex literal + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++
            suffix.map ofBool)

/-- The CNF-semantic out-of-range output is related to the unique canonical
CNF literal post-state whenever its index arithmetic is correct. -/
theorem canonical_defaultCNF_trailingBlankRel
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString)
    (hindex : cnfLiteralIndex literal = assignment.length + extraIndex) :
    trailingBlankRel blank
      (canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals assignment literal restLiteralPayload
        restPayload suffix)
      (defaultCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals assignment literal extraIndex
        restLiteralPayload restPayload suffix) := by
  cases suffix with
  | nil =>
      exact Or.inr (by
        simp [canonicalCNFLiteralEvaluatedConfig,
          defaultCNFLiteralEvaluatedConfig, appendTrailingBlank,
          configAt, tapeAt, hindex, List.append_assoc])
  | cons bit rest =>
      exact Or.inl (by
        simp [canonicalCNFLiteralEvaluatedConfig,
          defaultCNFLiteralEvaluatedConfig, hindex])


/-- A successful in-range positive lookup already has the unique canonical CNF
post-state once the assignment split is recombined. -/
theorem literalEvaluatedConfig_positive_eq_canonicalCNF
    (formulaValue clauseValue value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped tail restLiteralPayload restPayload suffix : BitString) :
    literalEvaluatedConfig formulaValue clauseValue true value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      tail suffix =
    canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
      remainingClauses remainingLiterals (skipped ++ value :: tail)
      (.positive skipped.length) restLiteralPayload restPayload suffix := by
  simp [literalEvaluatedConfig, canonicalCNFLiteralEvaluatedConfig,
    cnfLiteralIndex, CNF.Literal.eval, CNF.valueAt, applyPolarity,
    List.map_append, List.append_assoc]

/-- Negative literals have the same exact canonical recombination property. -/
theorem literalEvaluatedConfig_negative_eq_canonicalCNF
    (formulaValue clauseValue value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped tail restLiteralPayload restPayload suffix : BitString) :
    literalEvaluatedConfig formulaValue clauseValue false value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      tail suffix =
    canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
      remainingClauses remainingLiterals (skipped ++ value :: tail)
      (.negative skipped.length) restLiteralPayload restPayload suffix := by
  simp [literalEvaluatedConfig, canonicalCNFLiteralEvaluatedConfig,
    cnfLiteralIndex, CNF.Literal.eval, CNF.valueAt, applyPolarity,
    List.map_append, List.append_assoc]


/-- Every real CNF literal, in range or out of range, reaches one canonical
logical post-state up to at most the single redundant far-right blank. -/
theorem run_cnfLiteral_total_trailingBlankRel
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals assignment literal restLiteralPayload
        restPayload suffix)
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
          restLiteralPayload.length restPayload.length (cnfLiteralIndex literal))
        (firstLiteralSignConfig formulaValue clauseValue variableCount
          remainingClauses remainingLiterals (CNF.literalCodec.encode literal)
          restLiteralPayload restPayload assignment suffix)) := by
  cases literal with
  | positive index =>
      by_cases hlt : index < assignment.length
      · obtain ⟨skipped, value, tail, hsplit, hlen⟩ :=
          exists_assignment_split_of_lt assignment index hlt
        subst assignment
        rw [CNF.literalCodec_encode_positive_layout]
        rw [← hlen]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        have hlt' : skipped.length < (skipped ++ value :: tail).length := by
          simp
        rw [if_pos hlt']
        have hrun := run_literal_valid formulaValue clauseValue true value
          variableCount remainingClauses remainingLiterals skipped
          restLiteralPayload restPayload tail suffix
        rw [hrun]
        exact Or.inl
          (literalEvaluatedConfig_positive_eq_canonicalCNF formulaValue
            clauseValue value variableCount remainingClauses remainingLiterals
            skipped tail restLiteralPayload restPayload suffix)
      · let extraIndex := index - assignment.length
        have hindex : index = assignment.length + extraIndex := by
          unfold extraIndex
          omega
        simp only [cnfLiteralIndex]
        unfold cnfLiteralTotalEvaluationCost
        rw [if_neg hlt]
        change trailingBlankRel blank _
          (satControl.run
            (literalDefaultEvaluationCost assignment.length variableCount
              restLiteralPayload.length restPayload.length extraIndex)
            (firstLiteralSignConfig formulaValue clauseValue variableCount
              remainingClauses remainingLiterals
              (CNF.literalCodec.encode (.positive index)) restLiteralPayload
              restPayload assignment suffix))
        have hrun := run_cnfLiteral_default_extra formulaValue clauseValue
          variableCount remainingClauses remainingLiterals extraIndex assignment
          (.positive index) restLiteralPayload restPayload suffix (by
            simpa [cnfLiteralIndex] using hindex)
        rw [hrun]
        exact canonical_defaultCNF_trailingBlankRel formulaValue clauseValue
          variableCount remainingClauses remainingLiterals assignment
          (.positive index) extraIndex restLiteralPayload restPayload suffix (by
            simpa [cnfLiteralIndex] using hindex)
  | negative index =>
      by_cases hlt : index < assignment.length
      · obtain ⟨skipped, value, tail, hsplit, hlen⟩ :=
          exists_assignment_split_of_lt assignment index hlt
        subst assignment
        rw [CNF.literalCodec_encode_negative_layout]
        rw [← hlen]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        have hlt' : skipped.length < (skipped ++ value :: tail).length := by
          simp
        rw [if_pos hlt']
        have hrun := run_literal_valid formulaValue clauseValue false value
          variableCount remainingClauses remainingLiterals skipped
          restLiteralPayload restPayload tail suffix
        rw [hrun]
        exact Or.inl
          (literalEvaluatedConfig_negative_eq_canonicalCNF formulaValue
            clauseValue value variableCount remainingClauses remainingLiterals
            skipped tail restLiteralPayload restPayload suffix)
      · let extraIndex := index - assignment.length
        have hindex : index = assignment.length + extraIndex := by
          unfold extraIndex
          omega
        simp only [cnfLiteralIndex]
        unfold cnfLiteralTotalEvaluationCost
        rw [if_neg hlt]
        change trailingBlankRel blank _
          (satControl.run
            (literalDefaultEvaluationCost assignment.length variableCount
              restLiteralPayload.length restPayload.length extraIndex)
            (firstLiteralSignConfig formulaValue clauseValue variableCount
              remainingClauses remainingLiterals
              (CNF.literalCodec.encode (.negative index)) restLiteralPayload
              restPayload assignment suffix))
        have hrun := run_cnfLiteral_default_extra formulaValue clauseValue
          variableCount remainingClauses remainingLiterals extraIndex assignment
          (.negative index) restLiteralPayload restPayload suffix (by
            simpa [cnfLiteralIndex] using hindex)
        rw [hrun]
        exact canonical_defaultCNF_trailingBlankRel formulaValue clauseValue
          variableCount remainingClauses remainingLiterals assignment
          (.negative index) extraIndex restLiteralPayload restPayload suffix (by
            simpa [cnfLiteralIndex] using hindex)


/-- Any bounded continuation after a complete literal evaluation has the same
control state as the continuation from the unique canonical CNF post-state. -/
theorem run_after_cnfLiteral_total_state
    (steps : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    (satControl.run steps
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
          restLiteralPayload.length restPayload.length (cnfLiteralIndex literal))
        (firstLiteralSignConfig formulaValue clauseValue variableCount
          remainingClauses remainingLiterals (CNF.literalCodec.encode literal)
          restLiteralPayload restPayload assignment suffix))).state =
    (satControl.run steps
      (canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals assignment literal restLiteralPayload
        restPayload suffix)).state := by
  symm
  exact trailingBlankRel_run_state satControl steps _ _
    (run_cnfLiteral_total_trailingBlankRel formulaValue clauseValue variableCount
      remainingClauses remainingLiterals assignment literal restLiteralPayload
      restPayload suffix)

end SATMachineCertificatePhase
end OpenProblems.Complexity
