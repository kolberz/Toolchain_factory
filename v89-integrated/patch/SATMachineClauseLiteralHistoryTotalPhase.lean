import OpenProblems.Complexity.SATMachineClauseLiteralHistoryDefaultPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- One logical CNF-literal post-state before the already-processed prefix is
moved back across `clauseEnd`. -/
def historyCanonicalCNFLiteralEvaluatedRawConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let clauseTail :=
    List.replicate (processedLiterals + 1) clauseSpent ++
      List.replicate remainingLiterals clauseLive ++
        formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload :=
    List.replicate (cnfLiteralIndex literal + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  match processedWidth with
  | 0 =>
      configAt
        (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal)) blank
        clauseTail (clauseEnd :: payload)
  | p + 1 =>
      configAt
        (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal)) blank
        (List.replicate p processed ++ clauseEnd :: clauseTail)
        (processed :: payload)

/-- Canonical post-literal state after the old processed prefix has been moved
back to the right of `clauseEnd`. -/
def clauseHistoryPostLiteralConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal)) blank
    (List.replicate (processedLiterals + 1) clauseSpent ++
      List.replicate remainingLiterals clauseLive ++
        formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate processedWidth processed ++
      List.replicate (cnfLiteralIndex literal + 2) processed ++
        restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

theorem historyLiteralEvaluatedRaw_positive_eq_canonicalCNF
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped tail restLiteralPayload restPayload suffix : BitString) :
    historyLiteralEvaluatedRawConfig processedLiterals processedWidth
      formulaValue clauseValue true value variableCount remainingClauses
      remainingLiterals skipped restLiteralPayload restPayload tail suffix =
    historyCanonicalCNFLiteralEvaluatedRawConfig processedLiterals processedWidth
      formulaValue clauseValue variableCount remainingClauses remainingLiterals
      (skipped ++ value :: tail) (.positive skipped.length)
      restLiteralPayload restPayload suffix := by
  cases processedWidth <;>
    simp [historyLiteralEvaluatedRawConfig,
      historyCanonicalCNFLiteralEvaluatedRawConfig, cnfLiteralIndex,
      CNF.Literal.eval, CNF.valueAt, applyPolarity, List.map_append,
      List.append_assoc]

theorem historyLiteralEvaluatedRaw_negative_eq_canonicalCNF
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped tail restLiteralPayload restPayload suffix : BitString) :
    historyLiteralEvaluatedRawConfig processedLiterals processedWidth
      formulaValue clauseValue false value variableCount remainingClauses
      remainingLiterals skipped restLiteralPayload restPayload tail suffix =
    historyCanonicalCNFLiteralEvaluatedRawConfig processedLiterals processedWidth
      formulaValue clauseValue variableCount remainingClauses remainingLiterals
      (skipped ++ value :: tail) (.negative skipped.length)
      restLiteralPayload restPayload suffix := by
  cases processedWidth <;>
    simp [historyLiteralEvaluatedRawConfig,
      historyCanonicalCNFLiteralEvaluatedRawConfig, cnfLiteralIndex,
      CNF.Literal.eval, CNF.valueAt, applyPolarity, List.map_append,
      List.append_assoc]

theorem historyCanonical_defaultCNF_trailingBlankRel
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString)
    (hindex : cnfLiteralIndex literal = assignment.length + extraIndex) :
    trailingBlankRel blank
      (historyCanonicalCNFLiteralEvaluatedRawConfig processedLiterals processedWidth
        formulaValue clauseValue variableCount remainingClauses remainingLiterals
        assignment literal restLiteralPayload restPayload suffix)
      (historyDefaultLiteralEvaluatedRawConfig processedLiterals processedWidth
        formulaValue clauseValue (cnfLiteralPositive literal) variableCount
        remainingClauses remainingLiterals assignment extraIndex restLiteralPayload
        restPayload suffix) := by
  cases literal with
  | positive index =>
      simp only [cnfLiteralIndex, cnfLiteralPositive] at hindex ⊢
      subst index
      cases processedWidth <;> cases suffix with
      | nil =>
          exact Or.inr (by
            simp [historyCanonicalCNFLiteralEvaluatedRawConfig,
              historyDefaultLiteralEvaluatedRawConfig, appendTrailingBlank,
              configAt, tapeAt, CNF.Literal.eval, CNF.valueAt, applyPolarity,
              List.append_assoc])
      | cons bit rest =>
          exact Or.inl (by
            simp [historyCanonicalCNFLiteralEvaluatedRawConfig,
              historyDefaultLiteralEvaluatedRawConfig, CNF.Literal.eval,
              CNF.valueAt, applyPolarity, List.append_assoc])
  | negative index =>
      simp only [cnfLiteralIndex, cnfLiteralPositive] at hindex ⊢
      subst index
      cases processedWidth <;> cases suffix with
      | nil =>
          exact Or.inr (by
            simp [historyCanonicalCNFLiteralEvaluatedRawConfig,
              historyDefaultLiteralEvaluatedRawConfig, appendTrailingBlank,
              configAt, tapeAt, CNF.Literal.eval, CNF.valueAt, applyPolarity,
              List.append_assoc])
      | cons bit rest =>
          exact Or.inl (by
            simp [historyCanonicalCNFLiteralEvaluatedRawConfig,
              historyDefaultLiteralEvaluatedRawConfig, CNF.Literal.eval,
              CNF.valueAt, applyPolarity, List.append_assoc])

/-- Every CNF literal reaches the same history-aware logical raw post-state,
up to the single materialized far-right blank of the exhausted lookup branch. -/
theorem run_history_cnfLiteral_total_trailingBlankRel
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (historyCanonicalCNFLiteralEvaluatedRawConfig processedLiterals processedWidth
        formulaValue clauseValue variableCount remainingClauses remainingLiterals
        assignment literal restLiteralPayload restPayload suffix)
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
          restLiteralPayload.length restPayload.length (cnfLiteralIndex literal))
        (historyFirstLiteralSignConfig processedLiterals processedWidth
          formulaValue clauseValue variableCount remainingClauses remainingLiterals
          (CNF.literalCodec.encode literal) restLiteralPayload restPayload assignment
          suffix)) := by
  cases literal with
  | positive index =>
      by_cases hlt : index < assignment.length
      · obtain ⟨skipped, value, tail, hsplit, hlen⟩ :=
          exists_assignment_split_of_lt assignment index hlt
        subst assignment
        rw [CNF.literalCodec_encode_positive_layout]
        rw [← hlen]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        have hlt' : skipped.length < (skipped ++ value :: tail).length := by simp
        rw [if_pos hlt']
        have hrun := run_historyLiteral_valid processedLiterals processedWidth
          formulaValue clauseValue true value variableCount remainingClauses
          remainingLiterals skipped restLiteralPayload restPayload tail suffix
        rw [hrun]
        exact Or.inl
          (historyLiteralEvaluatedRaw_positive_eq_canonicalCNF processedLiterals
            processedWidth formulaValue clauseValue value variableCount
            remainingClauses remainingLiterals skipped tail restLiteralPayload
            restPayload suffix)
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
            (historyFirstLiteralSignConfig processedLiterals processedWidth
              formulaValue clauseValue variableCount remainingClauses
              remainingLiterals (CNF.literalCodec.encode (.positive index))
              restLiteralPayload restPayload assignment suffix))
        have hrun := run_historyLiteral_default_extra processedLiterals processedWidth
          formulaValue clauseValue true variableCount remainingClauses
          remainingLiterals extraIndex assignment restLiteralPayload restPayload suffix
        rw [show index = assignment.length + extraIndex by exact hindex]
        rw [CNF.literalCodec_encode_positive_layout]
        rw [hrun]
        exact historyCanonical_defaultCNF_trailingBlankRel processedLiterals
          processedWidth formulaValue clauseValue variableCount remainingClauses
          remainingLiterals assignment (.positive (assignment.length + extraIndex))
          extraIndex restLiteralPayload restPayload suffix rfl
  | negative index =>
      by_cases hlt : index < assignment.length
      · obtain ⟨skipped, value, tail, hsplit, hlen⟩ :=
          exists_assignment_split_of_lt assignment index hlt
        subst assignment
        rw [CNF.literalCodec_encode_negative_layout]
        rw [← hlen]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        have hlt' : skipped.length < (skipped ++ value :: tail).length := by simp
        rw [if_pos hlt']
        have hrun := run_historyLiteral_valid processedLiterals processedWidth
          formulaValue clauseValue false value variableCount remainingClauses
          remainingLiterals skipped restLiteralPayload restPayload tail suffix
        rw [hrun]
        exact Or.inl
          (historyLiteralEvaluatedRaw_negative_eq_canonicalCNF processedLiterals
            processedWidth formulaValue clauseValue value variableCount
            remainingClauses remainingLiterals skipped tail restLiteralPayload
            restPayload suffix)
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
            (historyFirstLiteralSignConfig processedLiterals processedWidth
              formulaValue clauseValue variableCount remainingClauses
              remainingLiterals (CNF.literalCodec.encode (.negative index))
              restLiteralPayload restPayload assignment suffix))
        have hrun := run_historyLiteral_default_extra processedLiterals processedWidth
          formulaValue clauseValue false variableCount remainingClauses
          remainingLiterals extraIndex assignment restLiteralPayload restPayload suffix
        rw [show index = assignment.length + extraIndex by exact hindex]
        rw [CNF.literalCodec_encode_negative_layout]
        rw [hrun]
        exact historyCanonical_defaultCNF_trailingBlankRel processedLiterals
          processedWidth formulaValue clauseValue variableCount remainingClauses
          remainingLiterals assignment (.negative (assignment.length + extraIndex))
          extraIndex restLiteralPayload restPayload suffix rfl

@[simp] theorem step_clauseFind_processed_history
    (formulaValue clauseValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseFind formulaValue clauseValue) blank
        (leftHead :: leftTail) (processed :: right)) =
    configAt (clauseFind formulaValue clauseValue) blank leftTail
      (leftHead :: processed :: right) := by
  cases formulaValue <;> cases clauseValue <;> rfl

/-- The old `processedWidth` cells are moved back across `clauseEnd` exactly. -/
theorem run_historyCanonicalRaw_normalize
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    satControl.run processedWidth
      (historyCanonicalCNFLiteralEvaluatedRawConfig processedLiterals processedWidth
        formulaValue clauseValue variableCount remainingClauses remainingLiterals
        assignment literal restLiteralPayload restPayload suffix) =
    clauseHistoryPostLiteralConfig processedLiterals processedWidth formulaValue
      clauseValue variableCount remainingClauses remainingLiterals assignment literal
      restLiteralPayload restPayload suffix := by
  let clauseTail : List SATMachineSymbol :=
    List.replicate (processedLiterals + 1) clauseSpent ++
      List.replicate remainingLiterals clauseLive ++
        formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload : List SATMachineSymbol :=
    List.replicate (cnfLiteralIndex literal + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  have hscan := run_keepLeft_markers
    (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal))
    (fun marker => marker = processed)
    (List.replicate processedWidth processed) clauseEnd clauseTail payload
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_clauseFind_processed_history formulaValue
        (clauseValue || CNF.Literal.eval assignment literal)
        leftHead leftTail right)
    (by
      intro marker hm
      exact List.eq_of_mem_replicate hm)
  simpa [historyCanonicalCNFLiteralEvaluatedRawConfig,
    clauseHistoryPostLiteralConfig, keepLeftScanConfig, clauseTail, payload,
    List.append_assoc] using hscan

/-- Total literal execution followed by old-prefix normalization reaches the
canonical history post-state, up to the same harmless trailing blank. -/
theorem run_history_cnfLiteral_total_normalized_trailingBlankRel
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (clauseHistoryPostLiteralConfig processedLiterals processedWidth formulaValue
        clauseValue variableCount remainingClauses remainingLiterals assignment literal
        restLiteralPayload restPayload suffix)
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
          restLiteralPayload.length restPayload.length (cnfLiteralIndex literal) +
          processedWidth)
        (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue
          clauseValue variableCount remainingClauses remainingLiterals
          (CNF.literalCodec.encode literal) restLiteralPayload restPayload assignment
          suffix)) := by
  have hrel := run_history_cnfLiteral_total_trailingBlankRel processedLiterals
    processedWidth formulaValue clauseValue variableCount remainingClauses
    remainingLiterals assignment literal restLiteralPayload restPayload suffix
  have hrun := trailingBlankRel_run satControl processedWidth _ _ hrel
  rw [run_historyCanonicalRaw_normalize] at hrun
  rw [controlMachine_run_add]
  exact hrun

/-- When a next literal exists, the normalized post-state is exactly the next
history-aware `clauseFind` configuration with updated `(j,P)`. -/
theorem clauseHistoryPostLiteralConfig_eq_nextFind
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses nextRemaining : Nat)
    (assignment : CNF.Assignment) (literal nextLiteral : CNF.Literal)
    (tailLiteralPayload restPayload suffix : BitString) :
    clauseHistoryPostLiteralConfig processedLiterals processedWidth formulaValue
      clauseValue variableCount remainingClauses (nextRemaining + 1) assignment literal
      (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload) restPayload suffix =
    clauseHistoryFindConfig formulaValue
      (clauseValue || CNF.Literal.eval assignment literal)
      variableCount remainingClauses (processedLiterals + 1) nextRemaining
      (processedWidth + cnfLiteralIndex literal + 2)
      (CNF.literalCodec.encode nextLiteral) tailLiteralPayload restPayload assignment
      suffix := by
  unfold clauseHistoryPostLiteralConfig clauseHistoryFindConfig
  rw [show processedWidth + cnfLiteralIndex literal + 2 =
      processedWidth + (cnfLiteralIndex literal + 2) by omega]
  rw [List.replicate_add]
  simp [List.map_append, List.append_assoc]

/-- One complete history-aware literal step, including normalization, lands on
next `clauseFind` up to the harmless trailing blank. -/
theorem run_history_cnfLiteral_total_to_nextFind_trailingBlankRel
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses nextRemaining : Nat)
    (assignment : CNF.Assignment) (literal nextLiteral : CNF.Literal)
    (tailLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (clauseHistoryFindConfig formulaValue
        (clauseValue || CNF.Literal.eval assignment literal)
        variableCount remainingClauses (processedLiterals + 1) nextRemaining
        (processedWidth + cnfLiteralIndex literal + 2)
        (CNF.literalCodec.encode nextLiteral) tailLiteralPayload restPayload assignment
        suffix)
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
          (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload).length
          restPayload.length (cnfLiteralIndex literal) + processedWidth)
        (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue
          clauseValue variableCount remainingClauses (nextRemaining + 1)
          (CNF.literalCodec.encode literal)
          (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload)
          restPayload assignment suffix)) := by
  have h := run_history_cnfLiteral_total_normalized_trailingBlankRel
    processedLiterals processedWidth formulaValue clauseValue variableCount
    remainingClauses (nextRemaining + 1) assignment literal
    (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload) restPayload suffix
  rw [clauseHistoryPostLiteralConfig_eq_nextFind] at h
  exact h

/-- Induction-ready transition: evaluate one literal, normalize the accumulated
processed prefix, then select the sign of the next literal. -/
theorem run_history_cnfLiteral_total_to_nextSign_trailingBlankRel
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses nextRemaining : Nat)
    (assignment : CNF.Assignment) (literal nextLiteral : CNF.Literal)
    (tailLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (clauseHistoryLiteralSignConfig formulaValue
        (clauseValue || CNF.Literal.eval assignment literal)
        variableCount remainingClauses (processedLiterals + 1) nextRemaining
        (processedWidth + cnfLiteralIndex literal + 2)
        (CNF.literalCodec.encode nextLiteral) tailLiteralPayload restPayload
        assignment suffix)
      (satControl.run
        (cnfLiteralTotalEvaluationCost assignment.length variableCount
            (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload).length
            restPayload.length (cnfLiteralIndex literal) +
          processedWidth +
          ((processedWidth + cnfLiteralIndex literal + 2) +
            2 * (processedLiterals + 1) + 4))
        (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue
          clauseValue variableCount remainingClauses (nextRemaining + 1)
          (CNF.literalCodec.encode literal)
          (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload)
          restPayload assignment suffix)) := by
  have hfind := run_history_cnfLiteral_total_to_nextFind_trailingBlankRel
    processedLiterals processedWidth formulaValue clauseValue variableCount
    remainingClauses nextRemaining assignment literal nextLiteral tailLiteralPayload
    restPayload suffix
  have hrun := trailingBlankRel_run satControl
    ((processedWidth + cnfLiteralIndex literal + 2) +
      2 * (processedLiterals + 1) + 4) _ _ hfind
  have hselect' :
      satControl.run
        ((processedWidth + cnfLiteralIndex literal + 2) +
          2 * (processedLiterals + 1) + 4)
        (clauseHistoryFindConfig formulaValue
          (clauseValue || CNF.Literal.eval assignment literal)
          variableCount remainingClauses (processedLiterals + 1) nextRemaining
          (processedWidth + cnfLiteralIndex literal + 2)
          (CNF.literalCodec.encode nextLiteral) tailLiteralPayload
          restPayload assignment suffix) =
      clauseHistoryLiteralSignConfig formulaValue
        (clauseValue || CNF.Literal.eval assignment literal)
        variableCount remainingClauses (processedLiterals + 1) nextRemaining
        (processedWidth + cnfLiteralIndex literal + 2)
        (CNF.literalCodec.encode nextLiteral) tailLiteralPayload restPayload
        assignment suffix := by
    cases nextLiteral with
    | positive index =>
        rw [CNF.literalCodec_encode_positive_layout]
        have h := run_clauseHistoryFind_to_literalSign formulaValue
          (clauseValue || CNF.Literal.eval assignment literal) true
          variableCount remainingClauses (processedLiterals + 1) nextRemaining
          (processedWidth + cnfLiteralIndex literal + 2)
          (List.replicate index true ++ [false]) tailLiteralPayload restPayload
          assignment suffix
        simpa [cnfLiteralIndex] using h
    | negative index =>
        rw [CNF.literalCodec_encode_negative_layout]
        have h := run_clauseHistoryFind_to_literalSign formulaValue
          (clauseValue || CNF.Literal.eval assignment literal) false
          variableCount remainingClauses (processedLiterals + 1) nextRemaining
          (processedWidth + cnfLiteralIndex literal + 2)
          (List.replicate index true ++ [false]) tailLiteralPayload restPayload
          assignment suffix
        simpa [cnfLiteralIndex] using h
  rw [hselect'] at hrun
  rw [show
    cnfLiteralTotalEvaluationCost assignment.length variableCount
        (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload).length
        restPayload.length (cnfLiteralIndex literal) + processedWidth +
      ((processedWidth + cnfLiteralIndex literal + 2) +
        2 * (processedLiterals + 1) + 4) =
    (cnfLiteralTotalEvaluationCost assignment.length variableCount
        (CNF.literalCodec.encode nextLiteral ++ tailLiteralPayload).length
        restPayload.length (cnfLiteralIndex literal) + processedWidth) +
      ((processedWidth + cnfLiteralIndex literal + 2) +
        2 * (processedLiterals + 1) + 4) by omega]
  rw [controlMachine_run_add]
  exact hrun

end SATMachineCertificatePhase
end OpenProblems.Complexity
