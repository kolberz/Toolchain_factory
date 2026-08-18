import OpenProblems.Complexity.SATMachineClauseRecursionPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- History-aware sign cursor with the same argument order as `firstLiteralSignConfig`. -/
def historyFirstLiteralSignConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (literalBits restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  clauseHistoryLiteralSignConfig formulaValue clauseValue variableCount
    remainingClauses processedLiterals remainingLiterals processedWidth
    literalBits restLiteralPayload restPayload assignment suffix

/-- History-aware post-sign/index-read entry state. -/
def historyLiteralIndexEntryConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (indexRead formulaValue clauseValue positive) blank
    (processed :: List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (List.replicate index (ofBool true) ++ ofBool false ::
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- History-aware lookup selector after unary index parsing. -/
def historyLiteralLookupSelectConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let baseLeft :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let right :=
    indexEnd :: restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  match index with
  | 0 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank baseLeft
        (processed :: right)
  | k + 1 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank
        (List.replicate k indexLive ++ processed :: baseLeft)
        (indexLive :: right)

/-- History-aware indexed lookup loop. -/
def historyLookupLoopConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (indexRemaining : Nat)
    (restLiteralPayload restPayload remainingAssignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let baseLeft :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let afterIndex :=
    List.replicate visited.length indexSpent ++ indexEnd ::
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentVisitedSymbol ++
            remainingAssignment.map assignmentSymbol ++ suffix.map ofBool
  match indexRemaining with
  | 0 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank baseLeft
        (processed :: afterIndex)
  | k + 1 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank
        (List.replicate k indexLive ++ processed :: baseLeft)
        (indexLive :: afterIndex)

/-- Raw return state after one history-aware valid literal evaluation, before
 the pre-existing processed prefix is normalized back across `clauseFind`. -/
def historyLiteralEvaluatedRawConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString)
    (restLiteralPayload restPayload assignmentTail suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let clauseTail :=
    List.replicate (processedLiterals + 1) clauseSpent ++
      List.replicate remainingLiterals clauseLive ++
        formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload :=
    List.replicate (visited.length + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentSymbol ++ assignmentSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool
  match processedWidth with
  | 0 =>
      configAt
        (clauseFind formulaValue (clauseValue || applyPolarity positive value)) blank
        clauseTail (clauseEnd :: payload)
  | p + 1 =>
      configAt
        (clauseFind formulaValue (clauseValue || applyPolarity positive value)) blank
        (List.replicate p processed ++ clauseEnd :: clauseTail)
        (processed :: payload)

theorem historyLiteralLookupSelectConfig_eq_historyLookupLoopConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    historyLiteralLookupSelectConfig processedLiterals processedWidth
      formulaValue clauseValue positive variableCount remainingClauses
      remainingLiterals index restLiteralPayload restPayload assignment suffix =
    historyLookupLoopConfig processedLiterals processedWidth
      formulaValue clauseValue positive variableCount remainingClauses
      remainingLiterals [] index restLiteralPayload restPayload assignment suffix := by
  cases index <;>
    simp [historyLiteralLookupSelectConfig, historyLookupLoopConfig, List.append_assoc]

theorem run_historyLiteralSign_to_indexRead
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run 1
      (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate index true ++ [false])
        restLiteralPayload restPayload assignment suffix) =
    historyLiteralIndexEntryConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  rw [controlMachine_run_one]
  unfold historyFirstLiteralSignConfig historyLiteralIndexEntryConfig
  simp only [List.map_append, List.map_cons, List.map_replicate, List.cons_append]
  rw [step_literalSign_raw]
  simp [List.append_assoc]


theorem run_historyIndexRead_to_lookupSelect
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run (index + 1)
      (historyLiteralIndexEntryConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals index restLiteralPayload restPayload
        assignment suffix) =
    historyLiteralLookupSelectConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  let baseLeft : List SATMachineSymbol :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload : List SATMachineSymbol :=
    ofBool false :: restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  have hscan := run_indexRead_trues formulaValue clauseValue positive index
    (processed :: baseLeft) payload
  have hscan' :
      satControl.run index
        (historyLiteralIndexEntryConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals index restLiteralPayload restPayload
          assignment suffix) =
      configAt (indexRead formulaValue clauseValue positive) blank
        (List.replicate index indexLive ++ processed :: baseLeft) payload := by
    unfold historyLiteralIndexEntryConfig baseLeft payload at hscan ⊢
    simpa [List.append_assoc] using hscan
  rw [show index + 1 = index + 1 by rfl]
  rw [controlMachine_run_add, hscan', controlMachine_run_one]
  cases index with
  | zero =>
      simp only [List.replicate_zero, List.nil_append]
      dsimp [payload]
      rw [step_indexRead_false]
      unfold historyLiteralLookupSelectConfig baseLeft
      simp [List.append_assoc]
  | succ k =>
      rw [List.replicate_succ]
      simp only [List.cons_append]
      dsimp [payload]
      rw [step_indexRead_false]
      unfold historyLiteralLookupSelectConfig baseLeft
      simp [List.append_assoc]


theorem run_historyLiteral_to_lookupSelect
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run (index + 2)
      (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate index true ++ [false])
        restLiteralPayload restPayload assignment suffix) =
    historyLiteralLookupSelectConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  rw [show index + 2 = 1 + (index + 1) by omega]
  rw [controlMachine_run_add]
  rw [run_historyLiteralSign_to_indexRead processedLiterals processedWidth]
  exact run_historyIndexRead_to_lookupSelect processedLiterals processedWidth formulaValue clauseValue positive
    variableCount remainingClauses remainingLiterals index restLiteralPayload
    restPayload assignment suffix


theorem run_historyLookupLoop_one
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals indexTail : Nat)
    (visited : BitString)
    (restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (4 * visited.length +
        2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + 9)
      (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited (indexTail + 1)
        restLiteralPayload restPayload (value :: assignmentTail) suffix) =
    historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals (visited ++ [value]) indexTail
      restLiteralPayload restPayload assignmentTail suffix := by
  let baseLeft : List SATMachineSymbol :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  let assignmentRight : List SATMachineSymbol :=
    assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool
  have hselect :
      satControl.run 1
        (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited (indexTail + 1)
          restLiteralPayload restPayload (value :: assignmentTail) suffix) =
      configAt (lookupSkipRight formulaValue clauseValue positive) blank
        (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ assignmentRight)) := by
    rw [controlMachine_run_one]
    unfold historyLookupLoopConfig baseLeft rightMarkers certMarkers assignmentRight
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    simp [List.append_assoc]
  have hright := run_keepRight_markers
    (lookupSkipRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers
    (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
    (separator :: certMarkers ++ assignmentRight)
    (step_lookupSkipRight_marker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupSkipRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ (indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft))
          (separator :: certMarkers ++ assignmentRight)) =
      configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ (indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft))
        (certMarkers ++ assignmentRight) := by
    rw [controlMachine_run_one]
    exact step_lookupSkipRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupSkipCertificate formulaValue clauseValue positive)
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ (indexSpent ::
      List.replicate indexTail indexLive ++ processed :: baseLeft))
    assignmentRight
    (step_lookupSkipCertificate_marker formulaValue clauseValue positive)
    (lookupSkipCertificateMarkers_all variableCount visited)
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hleftLayout :
      certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ (indexSpent ::
        List.replicate indexTail indexLive ++ processed :: baseLeft)) =
      returnMarkers ++ indexEnd ::
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft) := by
    unfold certMarkers rightMarkers returnMarkers
    unfold lookupSkipCertificateMarkers lookupSkipRightMarkers
    unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers zeroLookupRightMarkers
    simp [List.reverse_append, List.append_assoc]
  have hvalue :
      satControl.run 1
        (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ (indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)))
          assignmentRight) =
      keepLeftScanConfig (lookupReturnIndex formulaValue clauseValue positive)
        returnMarkers indexEnd
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft)
        (assignmentVisitedSymbol value ::
          assignmentTail.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [hleftLayout]
    unfold assignmentRight
    exact step_lookupSkipCertificate_assignment_keepLeft
      formulaValue clauseValue positive value returnMarkers indexEnd
      (List.replicate visited.length indexSpent ++ indexSpent ::
        List.replicate indexTail indexLive ++ processed :: baseLeft)
      (assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
      hreturnMarkers_ne
  have hreturn := run_keepLeft_markers
    (lookupReturnIndex formulaValue clauseValue positive)
    lookupReturnIndexMarker returnMarkers indexEnd
    (List.replicate visited.length indexSpent ++ indexSpent ::
      List.replicate indexTail indexLive ++ processed :: baseLeft)
    (assignmentVisitedSymbol value ::
      assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
    (step_lookupReturnIndex_marker formulaValue clauseValue positive)
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig (lookupReturnIndex formulaValue clauseValue positive)
          returnMarkers indexEnd
          (List.replicate visited.length indexSpent ++ indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (lookupReturnIndex formulaValue clauseValue positive) blank
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft)
        (indexEnd :: (returnMarkers.reverse ++
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool))) := by
    simpa only [List.cons_append] using hreturn
  have hend :
      satControl.run 1
        (configAt (lookupReturnIndex formulaValue clauseValue positive) blank
          (List.replicate visited.length indexSpent ++ indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)
          (indexEnd :: (returnMarkers.reverse ++
            (assignmentVisitedSymbol value ::
              assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))) =
      keepLeftScanConfig (lookupSelect formulaValue clauseValue positive)
        (List.replicate (visited.length + 1) indexSpent)
        (if indexTail = 0 then processed else indexLive)
        (if indexTail = 0 then baseLeft
          else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
        (indexEnd :: (returnMarkers.reverse ++
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool))) := by
    cases indexTail with
    | zero =>
        simpa only [Nat.zero_eq, if_true, Nat.zero_sub, List.replicate_zero,
          List.nil_append, List.append_nil, replicate_cons_same, List.cons_append] using
          (step_lookupReturnIndex_indexEnd_keepLeft
            formulaValue clauseValue positive
            (List.replicate (visited.length + 1) indexSpent)
            processed baseLeft
            (returnMarkers.reverse ++
              (assignmentVisitedSymbol value ::
                assignmentTail.map assignmentSymbol ++ suffix.map ofBool))
            (by simp))
    | succ k =>
        simpa only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
          replicate_cons_same, List.replicate_succ, List.cons_append,
          List.append_assoc] using
          (step_lookupReturnIndex_indexEnd_keepLeft
            formulaValue clauseValue positive
            (List.replicate (visited.length + 1) indexSpent)
            indexLive
            (List.replicate k indexLive ++ processed :: baseLeft)
            (returnMarkers.reverse ++
              (assignmentVisitedSymbol value ::
                assignmentTail.map assignmentSymbol ++ suffix.map ofBool))
            (by simp))
  have hspent :
      satControl.run (visited.length + 1)
        (keepLeftScanConfig (lookupSelect formulaValue clauseValue positive)
          (List.replicate (visited.length + 1) indexSpent)
          (if indexTail = 0 then processed else indexLive)
          (if indexTail = 0 then baseLeft
            else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
          (indexEnd :: (returnMarkers.reverse ++
            (assignmentVisitedSymbol value ::
              assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))) =
      historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals (visited ++ [value]) indexTail
        restLiteralPayload restPayload assignmentTail suffix := by
    have hscan := run_keepLeft_markers
      (lookupSelect formulaValue clauseValue positive)
      (fun marker => marker = indexSpent)
      (List.replicate (visited.length + 1) indexSpent)
      (if indexTail = 0 then processed else indexLive)
      (if indexTail = 0 then baseLeft
        else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
      (indexEnd :: (returnMarkers.reverse ++
        (assignmentVisitedSymbol value ::
          assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))
      (by
        intro marker hm leftHead leftTail right
        subst marker
        exact step_lookupSelect_spent formulaValue clauseValue positive
          leftHead leftTail right)
      (by simp)
    rw [List.length_replicate] at hscan
    rw [hscan]
    unfold historyLookupLoopConfig baseLeft
    unfold returnMarkers
    rw [lookupReturnIndexMarkers_reverse]
    cases indexTail with
    | zero =>
        simp [assignmentVisitedSymbol, List.map_append,
          zeroLookupCertificateMarkers, List.append_assoc]
    | succ k =>
        simp [assignmentVisitedSymbol, List.map_append,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
  have hlenRight : rightMarkers.length =
      visited.length + 1 + restLiteralPayload.length + restPayload.length := by
    exact lookupSkipRightMarkers_length _ _ _
  have hlenCert : certMarkers.length = variableCount + 1 + visited.length := by
    exact lookupSkipCertificateMarkers_length _ _
  have hlenReturn : returnMarkers.length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact lookupReturnIndexMarkers_length _ _ _ _
  rw [show 4 * visited.length + 2 * variableCount +
      2 * (restLiteralPayload.length + restPayload.length) + 9 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + (visited.length + 1))))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hvalue]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hend]
  exact hspent



theorem run_historyLookupLoop_target
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (4 * visited.length + 2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + 9)
      (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited 0
        restLiteralPayload restPayload (value :: assignmentTail) suffix) =
    historyLiteralEvaluatedRawConfig processedLiterals processedWidth formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals visited restLiteralPayload restPayload
      assignmentTail suffix := by
  let baseLeft : List SATMachineSymbol :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  let assignmentRight : List SATMachineSymbol :=
    assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hselect :
      satControl.run 1
        (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited 0
          restLiteralPayload restPayload (value :: assignmentTail) suffix) =
      configAt (lookupTargetRight formulaValue clauseValue positive) blank
        (processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ assignmentRight)) := by
    rw [controlMachine_run_one]
    unfold historyLookupLoopConfig baseLeft rightMarkers certMarkers assignmentRight
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    cases formulaValue <;> cases clauseValue <;> cases positive <;> cases value <;>
      simp [List.append_assoc]
    all_goals rfl
  have hright := run_keepRight_markers
    (lookupTargetRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers (processed :: baseLeft)
    (separator :: certMarkers ++ assignmentRight)
    (step_lookupTargetRight_lookupMarker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupTargetRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ processed :: baseLeft)
          (separator :: certMarkers ++ assignmentRight)) =
      configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ processed :: baseLeft)
        (certMarkers ++ assignmentRight) := by
    rw [controlMachine_run_one]
    exact step_lookupTargetRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupTargetCertificate formulaValue clauseValue positive)
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ processed :: baseLeft)
    assignmentRight
    (step_lookupTargetCertificate_lookupMarker formulaValue clauseValue positive)
    (lookupSkipCertificateMarkers_all variableCount visited)
  have hleftLayout :
      certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft) =
      returnMarkers ++ indexEnd ::
        (List.replicate visited.length indexSpent ++ processed :: baseLeft) := by
    unfold certMarkers rightMarkers returnMarkers
    unfold lookupSkipCertificateMarkers lookupSkipRightMarkers
    unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers zeroLookupRightMarkers
    simp [List.reverse_append, List.append_assoc]
  have hvalue :
      satControl.run 1
        (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft))
          assignmentRight) =
      keepLeftScanConfig
        (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
        returnMarkers indexEnd
        (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        (assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [hleftLayout]
    exact step_lookupTargetCertificate_assignment_keepLeft
      formulaValue clauseValue positive value returnMarkers indexEnd
      (List.replicate visited.length indexSpent ++ processed :: baseLeft)
      (assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
      hreturnMarkers_ne
  have hreturn := run_keepLeft_markers
    (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
    lookupReturnIndexMarker returnMarkers indexEnd
    (List.replicate visited.length indexSpent ++ processed :: baseLeft)
    (assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
    (step_cleanupReturn_marker formulaValue clauseValue (applyPolarity positive value))
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig
          (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          returnMarkers indexEnd
          (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          (assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value)) blank
        (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        (indexEnd :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight) := by
    simpa [assignmentRight] using hreturn
  have hindexEnd :
      satControl.run 1
        (configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value)) blank
          (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          (indexEnd :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) =
      keepLeftScanConfig (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
        (List.replicate visited.length indexSpent) processed baseLeft
        (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight) := by
    exact step_cleanupReturn_indexEnd_keepLeft formulaValue clauseValue
      (applyPolarity positive value) (List.replicate visited.length indexSpent)
      processed baseLeft
      ((returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)
  have hspent := run_keepLeft_markers
    (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
    (fun marker => marker = indexSpent)
    (List.replicate visited.length indexSpent) processed baseLeft
    (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_cleanupIndex_spent formulaValue clauseValue
        (applyPolarity positive value) leftHead leftTail right)
    (by simp)
  have hspent' :
      satControl.run visited.length
        (keepLeftScanConfig (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
          (List.replicate visited.length indexSpent) processed baseLeft
          (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) =
      configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value)) blank baseLeft
        (processed ::
          ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
            processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight) := by
    simpa using hspent
  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
          blank baseLeft
          (processed ::
            ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
              processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) =
      historyLiteralEvaluatedRawConfig processedLiterals processedWidth formulaValue clauseValue positive value variableCount
        remainingClauses remainingLiterals visited restLiteralPayload restPayload
        assignmentTail suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    cases processedWidth with
    | zero =>
        simp only [List.replicate_zero, List.nil_append, List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold historyLiteralEvaluatedRawConfig assignmentRight returnMarkers
        simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
    | succ p =>
        rw [List.replicate_succ]
        simp only [List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold historyLiteralEvaluatedRawConfig assignmentRight returnMarkers
        simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
  have hlenRight : rightMarkers.length =
      visited.length + 1 + restLiteralPayload.length + restPayload.length := by
    exact lookupSkipRightMarkers_length _ _ _
  have hlenCert : certMarkers.length = variableCount + 1 + visited.length := by
    exact lookupSkipCertificateMarkers_length _ _
  have hlenReturn : returnMarkers.length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact lookupReturnIndexMarkers_length _ _ _ _
  rw [show 4 * visited.length + 2 * variableCount +
      2 * (restLiteralPayload.length + restPayload.length) + 9 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + (visited.length + 1))))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hvalue]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hindexEnd]
  rw [controlMachine_run_add, hspent']
  exact hclean


theorem run_historyLookupLoop_prefix
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (lookupSkipCostFrom visited.length variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited skipped.length
        restLiteralPayload restPayload (skipped ++ assignmentTail) suffix) =
    historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals (visited ++ skipped) 0
      restLiteralPayload restPayload assignmentTail suffix := by
  induction skipped generalizing visited with
  | nil =>
      simp [lookupSkipCostFrom, historyLookupLoopConfig]
  | cons value rest ih =>
      change satControl.run
        (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
            restPayload.length +
          lookupSkipCostFrom (visited.length + 1) variableCount
            restLiteralPayload.length restPayload.length rest.length)
        (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited (rest.length + 1)
          restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) = _
      rw [controlMachine_run_add]
      have hone := run_historyLookupLoop_one processedLiterals processedWidth
        formulaValue clauseValue positive value variableCount remainingClauses
        remainingLiterals rest.length visited restLiteralPayload restPayload
        (rest ++ assignmentTail) suffix
      have hone' :
          satControl.run
            (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
              restPayload.length)
            (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
              remainingClauses remainingLiterals visited (rest.length + 1)
              restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) =
          historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
            remainingClauses remainingLiterals (visited ++ [value]) rest.length
            restLiteralPayload restPayload (rest ++ assignmentTail) suffix := by
        simpa [lookupSkipOneCost] using hone
      rw [hone']
      have hrest := ih (visited := visited ++ [value])
      simpa [List.append_assoc] using hrest


theorem run_historyLiteralLookup_valid
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (literalLookupCost variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (historyLiteralLookupSelectConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals skipped.length
        restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
    historyLiteralEvaluatedRawConfig processedLiterals processedWidth formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      assignmentTail suffix := by
  have hstart := historyLiteralLookupSelectConfig_eq_historyLookupLoopConfig processedLiterals processedWidth
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals skipped.length restLiteralPayload restPayload
    (skipped ++ value :: assignmentTail) suffix
  have hskip := run_historyLookupLoop_prefix processedLiterals processedWidth
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals ([] : BitString) skipped restLiteralPayload restPayload
    (value :: assignmentTail) suffix
  have htarget := run_historyLookupLoop_target processedLiterals processedWidth
    formulaValue clauseValue positive value variableCount remainingClauses
    remainingLiterals skipped restLiteralPayload restPayload assignmentTail suffix
  have hskip' :
      satControl.run
        (lookupSkipCostFrom 0 variableCount restLiteralPayload.length
          restPayload.length skipped.length)
        (historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals [] skipped.length
          restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
      historyLookupLoopConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals skipped 0 restLiteralPayload restPayload
        (value :: assignmentTail) suffix := by
    simpa using hskip
  unfold literalLookupCost
  rw [controlMachine_run_add]
  rw [hstart]
  rw [hskip']
  simpa [lookupSkipOneCost] using htarget


theorem run_historyLiteral_valid
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (literalEvaluationCost variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (historyFirstLiteralSignConfig processedLiterals processedWidth formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate skipped.length true ++ [false])
        restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
    historyLiteralEvaluatedRawConfig processedLiterals processedWidth formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      assignmentTail suffix := by
  have hparse := run_historyLiteral_to_lookupSelect processedLiterals processedWidth
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals skipped.length restLiteralPayload restPayload
    (skipped ++ value :: assignmentTail) suffix
  have hlookup := run_historyLiteralLookup_valid processedLiterals processedWidth
    formulaValue clauseValue positive value variableCount remainingClauses
    remainingLiterals skipped restLiteralPayload restPayload assignmentTail suffix
  unfold literalEvaluationCost
  rw [controlMachine_run_add, hparse]
  exact hlookup

end SATMachineCertificatePhase
end OpenProblems.Complexity
