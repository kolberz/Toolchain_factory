import OpenProblems.Complexity.SATMachineTrailingBlankPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- Canonical `clauseFind` cursor after `processedLiterals` literals have been
fully evaluated and normalized back to the clause-end marker.  The already
processed literal encodings occupy `processedWidth` tape cells immediately to
the right of `clauseEnd`.  At least one live literal remains; the distinguished
next literal is followed by `remainingLiterals` further literals. -/
def clauseHistoryFindConfig
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses processedLiterals remainingLiterals
      processedWidth : Nat)
    (nextLiteralBits restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (clauseFind formulaValue clauseValue) blank
    (List.replicate processedLiterals clauseSpent ++
      List.replicate (remainingLiterals + 1) clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate processedWidth processed ++
      nextLiteralBits.map ofBool ++ restLiteralPayload.map ofBool ++
        restPayload.map ofBool ++ separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- Canonical sign cursor for a literal selected after arbitrary earlier
literal history in the same clause.  Earlier encoded literal cells have been
crossed into the left zipper and every selected literal marker is spent. -/
def clauseHistoryLiteralSignConfig
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses processedLiterals remainingLiterals
      processedWidth : Nat)
    (literalBits restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (literalSign formulaValue clauseValue) blank
    (List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (literalBits.map ofBool ++ restLiteralPayload.map ofBool ++
      restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

@[simp] theorem step_clauseFind_clauseEnd_history
    (formulaValue clauseValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseFind formulaValue clauseValue) blank
        (leftHead :: leftTail) (clauseEnd :: right)) =
    configAt (clauseFind formulaValue clauseValue) blank leftTail
      (leftHead :: clauseEnd :: right) := by
  cases formulaValue <;> cases clauseValue <;> rfl

@[simp] theorem step_clauseFind_spent_history
    (formulaValue clauseValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseFind formulaValue clauseValue) blank
        (leftHead :: leftTail) (clauseSpent :: right)) =
    configAt (clauseFind formulaValue clauseValue) blank leftTail
      (leftHead :: clauseSpent :: right) := by
  cases formulaValue <;> cases clauseValue <;> rfl

/-- Markers crossed on the way from the newly spent literal marker back to the
next raw literal sign. -/
def clauseHistoryCursorMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = clauseSpent ∨ symbol = clauseEnd ∨ symbol = processed

@[simp] theorem step_clauseToCursor_historyMarker
    (formulaValue clauseValue : Bool)
    (symbol : SATMachineSymbol)
    (h : clauseHistoryCursorMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseToCursor formulaValue clauseValue) blank left
        (symbol :: right)) =
    configAt (clauseToCursor formulaValue clauseValue) blank
      (symbol :: left) right := by
  rcases h with rfl | rfl | rfl <;>
    cases formulaValue <;> cases clauseValue <;> rfl

/-- The complete arbitrary-history selector.  After `j` earlier literals with
`p` processed encoding cells, selecting the next live literal costs exactly
`p + 2*j + 4` transitions and lands on the next sign bit with the history
layout made explicit. -/
theorem run_clauseHistoryFind_to_literalSign
    (formulaValue clauseValue sign : Bool)
    (variableCount remainingClauses processedLiterals remainingLiterals
      processedWidth : Nat)
    (literalRest restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run (processedWidth + 2 * processedLiterals + 4)
      (clauseHistoryFindConfig formulaValue clauseValue variableCount
        remainingClauses processedLiterals remainingLiterals processedWidth
        (sign :: literalRest) restLiteralPayload restPayload assignment suffix) =
    clauseHistoryLiteralSignConfig formulaValue clauseValue variableCount
      remainingClauses processedLiterals remainingLiterals processedWidth
      (sign :: literalRest) restLiteralPayload restPayload assignment suffix := by
  let outerLeft : List SATMachineSymbol :=
    List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let literalRight : List SATMachineSymbol :=
    ofBool sign :: literalRest.map ofBool ++ restLiteralPayload.map ofBool ++
      restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  let spentMarkers : List SATMachineSymbol :=
    List.replicate processedLiterals clauseSpent
  let cursorMarkers : List SATMachineSymbol :=
    spentMarkers ++ clauseEnd :: List.replicate processedWidth processed
  have hfirst :
      satControl.run 1
        (clauseHistoryFindConfig formulaValue clauseValue variableCount
          remainingClauses processedLiterals remainingLiterals processedWidth
          (sign :: literalRest) restLiteralPayload restPayload assignment suffix) =
      keepLeftScanConfig (clauseFind formulaValue clauseValue)
        spentMarkers clauseLive outerLeft
        (clauseEnd :: List.replicate processedWidth processed ++ literalRight) := by
    rw [controlMachine_run_one]
    unfold clauseHistoryFindConfig spentMarkers outerLeft literalRight
    cases processedLiterals with
    | zero =>
        have hstep := step_clauseFind_clauseEnd_history formulaValue clauseValue
          clauseLive
          (List.replicate remainingLiterals clauseLive ++
            formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
              variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (List.replicate processedWidth processed ++
            ofBool sign :: literalRest.map ofBool ++ restLiteralPayload.map ofBool ++
              restPayload.map ofBool ++ separator ::
                List.replicate variableCount assignmentLengthChecked ++
                  assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
        simpa [keepLeftScanConfig, List.replicate_succ, List.append_assoc] using hstep
    | succ n =>
        have hstep := step_clauseFind_clauseEnd_history formulaValue clauseValue
          clauseSpent
          (List.replicate n clauseSpent ++
            List.replicate (remainingLiterals + 1) clauseLive ++
              formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
                variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (List.replicate processedWidth processed ++
            ofBool sign :: literalRest.map ofBool ++ restLiteralPayload.map ofBool ++
              restPayload.map ofBool ++ separator ::
                List.replicate variableCount assignmentLengthChecked ++
                  assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
        simpa [keepLeftScanConfig, List.replicate_succ, List.append_assoc] using hstep
  have hspent := run_keepLeft_markers
    (clauseFind formulaValue clauseValue)
    (fun symbol => symbol = clauseSpent)
    spentMarkers clauseLive outerLeft
    (clauseEnd :: List.replicate processedWidth processed ++ literalRight)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_clauseFind_spent_history formulaValue clauseValue
        leftHead leftTail right)
    (by
      intro marker hm
      unfold spentMarkers at hm
      exact List.eq_of_mem_replicate hm)
  have hspent' :
      satControl.run processedLiterals
        (keepLeftScanConfig (clauseFind formulaValue clauseValue)
          spentMarkers clauseLive outerLeft
          (clauseEnd :: List.replicate processedWidth processed ++ literalRight)) =
      configAt (clauseFind formulaValue clauseValue) blank outerLeft
        (clauseLive :: spentMarkers.reverse ++ clauseEnd ::
          List.replicate processedWidth processed ++ literalRight) := by
    simpa [spentMarkers] using hspent
  have hlive :
      satControl.run 1
        (configAt (clauseFind formulaValue clauseValue) blank outerLeft
          (clauseLive :: spentMarkers.reverse ++ clauseEnd ::
            List.replicate processedWidth processed ++ literalRight)) =
      configAt (clauseToCursor formulaValue clauseValue) blank
        (clauseSpent :: outerLeft)
        (cursorMarkers ++ literalRight) := by
    rw [controlMachine_run_one]
    have hstep := step_clauseFind_live formulaValue clauseValue outerLeft
      (spentMarkers.reverse ++ clauseEnd ::
        List.replicate processedWidth processed ++ literalRight)
    simpa [cursorMarkers, spentMarkers, List.append_assoc] using hstep
  have hcursorAll : ∀ marker ∈ cursorMarkers, clauseHistoryCursorMarker marker := by
    intro marker hm
    unfold cursorMarkers spentMarkers at hm
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hm
    rcases hm with hspentMem | hend | hprocessed
    · exact Or.inl hspentMem.2
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr hprocessed.2)
  have hcursor := run_keepRight_markers
    (clauseToCursor formulaValue clauseValue)
    clauseHistoryCursorMarker cursorMarkers
    (clauseSpent :: outerLeft) literalRight
    (step_clauseToCursor_historyMarker formulaValue clauseValue)
    hcursorAll
  have hcursor' :
      satControl.run (processedLiterals + 1 + processedWidth)
        (configAt (clauseToCursor formulaValue clauseValue) blank
          (clauseSpent :: outerLeft) (cursorMarkers ++ literalRight)) =
      configAt (clauseToCursor formulaValue clauseValue) blank
        (List.replicate processedWidth processed ++ clauseEnd ::
          List.replicate (processedLiterals + 1) clauseSpent ++ outerLeft)
        literalRight := by
    have hlen : cursorMarkers.length = processedLiterals + 1 + processedWidth := by
      unfold cursorMarkers spentMarkers
      simp
    rw [← hlen]
    rw [hcursor]
    unfold cursorMarkers spentMarkers outerLeft literalRight
    simp [List.reverse_append, List.replicate_succ, List.append_assoc,
      replicate_append_same_marker]
    omega
  have hraw :
      satControl.run 1
        (configAt (clauseToCursor formulaValue clauseValue) blank
          (List.replicate processedWidth processed ++ clauseEnd ::
            List.replicate (processedLiterals + 1) clauseSpent ++ outerLeft)
          literalRight) =
      clauseHistoryLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses processedLiterals remainingLiterals processedWidth
        (sign :: literalRest) restLiteralPayload restPayload assignment suffix := by
    rw [controlMachine_run_one]
    have hstep := step_clauseToCursor_raw formulaValue clauseValue sign
      (List.replicate processedWidth processed ++ clauseEnd ::
        List.replicate (processedLiterals + 1) clauseSpent ++ outerLeft)
      (literalRest.map ofBool ++ restLiteralPayload.map ofBool ++
        restPayload.map ofBool ++ separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    simpa [literalRight, clauseHistoryLiteralSignConfig, outerLeft,
      List.append_assoc] using hstep
  rw [show processedWidth + 2 * processedLiterals + 4 =
      1 + (processedLiterals + (1 +
        ((processedLiterals + 1 + processedWidth) + 1))) by omega]
  rw [controlMachine_run_add, hfirst]
  rw [controlMachine_run_add, hspent']
  rw [controlMachine_run_add, hlive]
  rw [controlMachine_run_add, hcursor']
  exact hraw

end SATMachineCertificatePhase
end OpenProblems.Complexity
