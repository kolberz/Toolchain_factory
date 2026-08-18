import OpenProblems.Complexity.SATMachineVariablePhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState

@[simp] theorem step_formulaLength_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt formulaLength blank left (ofBool true :: right)) =
    configAt formulaLength blank (formulaLive :: left) right := by
  rfl

/-- Exact scan of the unary formula/clause count. -/
theorem run_formulaLength_trues
    (n : Nat) (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt formulaLength blank left
        (List.replicate n (ofBool true) ++ payload)) =
    configAt formulaLength blank
      (List.replicate n formulaLive ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by omega]
      rw [controlMachine_run_add, controlMachine_run_one]
      simp only [List.cons_append]
      rw [step_formulaLength_true]
      simpa [List.replicate_succ, List.append_assoc, Nat.add_comm,
        replicate_append_same_marker] using
        (ih (left := formulaLive :: left))

@[simp] theorem step_formulaLength_false
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt formulaLength blank (leftHead :: leftTail)
        (ofBool false :: right)) =
    configAt (formulaFind true) blank leftTail
      (leftHead :: formulaEnd :: right) := by
  rfl

/-- Canonical state immediately after the formula-count terminator when at
least one clause remains. -/
def formulaFindFirstConfig
    (variableCount remainingClauses : Nat)
    (clausePayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (formulaFind true) blank
    (List.replicate remainingClauses formulaLive ++
      variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (formulaLive :: formulaEnd :: clausePayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- Positive formula count reaches the first formula-live marker exactly. -/
theorem run_formulaLength_prefix_to_find
    (variableCount remainingClauses : Nat)
    (clausePayload assignment suffix : BitString) :
    satControl.run (remainingClauses + 2)
      (formulaLengthEntryConfig variableCount
        (List.replicate (remainingClauses + 1) true ++ false :: clausePayload)
        assignment suffix) =
    formulaFindFirstConfig variableCount remainingClauses
      clausePayload assignment suffix := by
  have hscan := run_formulaLength_trues (remainingClauses + 1)
    (variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (ofBool false :: clausePayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hscan' :
      satControl.run (remainingClauses + 1)
        (formulaLengthEntryConfig variableCount
          (List.replicate (remainingClauses + 1) true ++ false :: clausePayload)
          assignment suffix) =
      configAt formulaLength blank
        (List.replicate remainingClauses formulaLive ++ formulaLive ::
          variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (ofBool false :: clausePayload.map ofBool ++ separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    unfold formulaLengthEntryConfig at hscan ⊢
    simpa [List.map_append, List.replicate_succ, List.append_assoc,
      replicate_append_same_marker] using hscan
  rw [show remainingClauses + 2 = (remainingClauses + 1) + 1 by omega]
  rw [controlMachine_run_add, hscan', controlMachine_run_one]
  cases remainingClauses with
  | zero =>
      unfold formulaFindFirstConfig
      rfl
  | succ n =>
      unfold formulaFindFirstConfig
      simp only [List.replicate_succ, List.cons_append]
      simp [List.append_assoc, replicate_append_same_marker]
      rw [List.replicate_succ]
      rfl

@[simp] theorem step_formulaFind_live_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (formulaFind true) blank left (formulaLive :: right)) =
    configAt (formulaToCursor true) blank (formulaSpent :: left) right := by
  rfl

@[simp] theorem step_formulaToCursor_formulaEnd_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (formulaToCursor true) blank left (formulaEnd :: right)) =
    configAt (formulaToCursor true) blank (formulaEnd :: left) right := by
  rfl

@[simp] theorem step_formulaToCursor_raw_true
    (left right : List SATMachineSymbol) (bit : Bool) :
    satControl.stepConfig
      (configAt (formulaToCursor true) blank left (ofBool bit :: right)) =
    configAt (clauseLength true) blank left (ofBool bit :: right) := by
  cases bit <;> rfl

/-- Canonical first-clause cursor after selecting the rightmost formula-live
marker. -/
def firstClauseLengthConfig
    (variableCount remainingClauses : Nat)
    (clauseBits restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (clauseLength true) blank
    (formulaEnd :: formulaSpent ::
      List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseBits.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- Once a nonempty clause encoding is under the formula cursor, selection of
the first formula marker reaches `clauseLength true` in three additional
steps. -/
theorem run_formulaFind_to_firstClause
    (variableCount remainingClauses : Nat)
    (firstBit : Bool) (clauseRest restPayload assignment suffix : BitString) :
    satControl.run 3
      (formulaFindFirstConfig variableCount remainingClauses
        ((firstBit :: clauseRest) ++ restPayload) assignment suffix) =
    firstClauseLengthConfig variableCount remainingClauses
      (firstBit :: clauseRest) restPayload assignment suffix := by
  have h1 :
      satControl.run 1
        (formulaFindFirstConfig variableCount remainingClauses
          ((firstBit :: clauseRest) ++ restPayload) assignment suffix) =
      configAt (formulaToCursor true) blank
        (formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (formulaEnd :: (firstBit :: clauseRest).map ofBool ++
          restPayload.map ofBool ++ separator ::
            List.replicate variableCount assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold formulaFindFirstConfig
    simp only [List.map_append, List.map_cons, List.cons_append]
    rw [step_formulaFind_live_true]
  have h2 :
      satControl.run 1
        (configAt (formulaToCursor true) blank
          (formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (formulaEnd :: (firstBit :: clauseRest).map ofBool ++
            restPayload.map ofBool ++ separator ::
              List.replicate variableCount assignmentLengthChecked ++
                assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (formulaToCursor true) blank
        (formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        ((firstBit :: clauseRest).map ofBool ++
          restPayload.map ofBool ++ separator ::
            List.replicate variableCount assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_formulaToCursor_formulaEnd_true]
  have h3 :
      satControl.run 1
        (configAt (formulaToCursor true) blank
          (formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          ((firstBit :: clauseRest).map ofBool ++
            restPayload.map ofBool ++ separator ::
              List.replicate variableCount assignmentLengthChecked ++
                assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      firstClauseLengthConfig variableCount remainingClauses
        (firstBit :: clauseRest) restPayload assignment suffix := by
    rw [controlMachine_run_one]
    simp only [List.map_cons, List.cons_append]
    rw [step_formulaToCursor_raw_true]
    unfold firstClauseLengthConfig
    simp [List.append_assoc]
  rw [show 3 = 1 + (1 + 1) by omega]
  rw [controlMachine_run_add, h1]
  rw [controlMachine_run_add, h2]
  exact h3

@[simp] theorem step_formulaFind_end_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (formulaFind true) blank left (variableEnd :: right)) =
    configAt (formulaDoneToCursor true) blank (variableEnd :: left) right := by
  rfl

@[simp] theorem step_formulaDone_formulaEnd_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (formulaDoneToCursor true) blank left (formulaEnd :: right)) =
    configAt (formulaDoneToCursor true) blank (formulaEnd :: left) right := by
  rfl

@[simp] theorem step_formulaDone_separator_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (formulaDoneToCursor true) blank left (separator :: right)) =
    configAt accept blank left (separator :: right) := by
  rfl

/-- Empty CNF formula evaluates to true in four exact machine steps from the
formula-length state. -/
theorem run_emptyFormula_to_accept
    (variableCount : Nat) (assignment suffix : BitString) :
    satControl.run 4
      (formulaLengthEntryConfig variableCount [false] assignment suffix) =
    configAt accept blank
      (formulaEnd :: variableEnd ::
        List.replicate variableCount variableChecked ++ [blank])
      (separator :: List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
  have h1 :
      satControl.run 1
        (formulaLengthEntryConfig variableCount [false] assignment suffix) =
      configAt (formulaFind true) blank
        (List.replicate variableCount variableChecked ++ [blank])
        (variableEnd :: formulaEnd :: separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold formulaLengthEntryConfig
    rfl
  have h2 :
      satControl.run 1
        (configAt (formulaFind true) blank
          (List.replicate variableCount variableChecked ++ [blank])
          (variableEnd :: formulaEnd :: separator ::
            List.replicate variableCount assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (formulaDoneToCursor true) blank
        (variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (formulaEnd :: separator :: List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_formulaFind_end_true]
  have h3 :
      satControl.run 1
        (configAt (formulaDoneToCursor true) blank
          (variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (formulaEnd :: separator :: List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (formulaDoneToCursor true) blank
        (formulaEnd :: variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (separator :: List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_formulaDone_formulaEnd_true]
  have h4 :
      satControl.run 1
        (configAt (formulaDoneToCursor true) blank
          (formulaEnd :: variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (separator :: List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt accept blank
        (formulaEnd :: variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (separator :: List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_formulaDone_separator_true]
  rw [show 4 = 1 + (1 + (1 + 1)) by omega]
  rw [controlMachine_run_add, h1]
  rw [controlMachine_run_add, h2]
  rw [controlMachine_run_add, h3]
  exact h4

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

@[simp] theorem step_clauseLength_true
    (formulaValue : Bool) (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseLength formulaValue) blank left (ofBool true :: right)) =
    configAt (clauseLength formulaValue) blank (clauseLive :: left) right := by
  cases formulaValue <;> rfl

/-- Exact unary scan of one clause's literal count. -/
theorem run_clauseLength_trues
    (formulaValue : Bool) (n : Nat)
    (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt (clauseLength formulaValue) blank left
        (List.replicate n (ofBool true) ++ payload)) =
    configAt (clauseLength formulaValue) blank
      (List.replicate n clauseLive ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show n + 1 = 1 + n by omega]
      rw [controlMachine_run_add, controlMachine_run_one]
      rw [step_clauseLength_true]
      simpa [List.replicate_succ, List.append_assoc, Nat.add_comm,
        replicate_append_same_marker] using
        (ih (left := clauseLive :: left))

@[simp] theorem step_clauseLength_false
    (formulaValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseLength formulaValue) blank (leftHead :: leftTail)
        (ofBool false :: right)) =
    configAt (clauseFind formulaValue false) blank leftTail
      (leftHead :: clauseEnd :: right) := by
  cases formulaValue <;> rfl

/-- Canonical state after a positive literal-count terminator. -/
def clauseFindFirstConfig
    (formulaValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (literalPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (clauseFind formulaValue false) blank
    (List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseLive :: clauseEnd :: literalPayload.map ofBool ++
      restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- Positive literal count in the first clause reaches the rightmost live literal marker exactly. -/
theorem run_clauseLength_prefix_to_find
    (variableCount remainingClauses remainingLiterals : Nat)
    (literalPayload restPayload assignment suffix : BitString) :
    satControl.run (remainingLiterals + 2)
      (firstClauseLengthConfig variableCount remainingClauses
        (List.replicate (remainingLiterals + 1) true ++ false :: literalPayload)
        restPayload assignment suffix) =
    clauseFindFirstConfig true variableCount remainingClauses
      remainingLiterals literalPayload restPayload assignment suffix := by
  have hscan := run_clauseLength_trues true (remainingLiterals + 1)
    (formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
      variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (ofBool false :: literalPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hscan' :
      satControl.run (remainingLiterals + 1)
        (firstClauseLengthConfig variableCount remainingClauses
          (List.replicate (remainingLiterals + 1) true ++ false :: literalPayload)
          restPayload assignment suffix) =
      configAt (clauseLength true) blank
        (List.replicate remainingLiterals clauseLive ++ clauseLive ::
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (ofBool false :: literalPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
          List.replicate variableCount assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    unfold firstClauseLengthConfig at hscan ⊢
    simpa [List.map_append, List.replicate_succ, List.append_assoc,
      replicate_append_same_marker] using hscan
  rw [show remainingLiterals + 2 = (remainingLiterals + 1) + 1 by omega]
  rw [controlMachine_run_add, hscan', controlMachine_run_one]
  cases remainingLiterals with
  | zero =>
      unfold clauseFindFirstConfig
      rfl
  | succ n =>
      unfold clauseFindFirstConfig
      simp only [List.replicate_succ, List.cons_append]
      simp [List.append_assoc, replicate_append_same_marker]
      rw [List.replicate_succ]
      rfl

@[simp] theorem step_clauseFind_live
    (formulaValue clauseValue : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseFind formulaValue clauseValue) blank left (clauseLive :: right)) =
    configAt (clauseToCursor formulaValue clauseValue) blank
      (clauseSpent :: left) right := by
  cases formulaValue <;> cases clauseValue <;> rfl

@[simp] theorem step_clauseToCursor_clauseEnd
    (formulaValue clauseValue : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseToCursor formulaValue clauseValue) blank left (clauseEnd :: right)) =
    configAt (clauseToCursor formulaValue clauseValue) blank
      (clauseEnd :: left) right := by
  cases formulaValue <;> cases clauseValue <;> rfl

@[simp] theorem step_clauseToCursor_raw
    (formulaValue clauseValue bit : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (clauseToCursor formulaValue clauseValue) blank left (ofBool bit :: right)) =
    configAt (literalSign formulaValue clauseValue) blank left (ofBool bit :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases bit <;> rfl

/-- Canonical cursor at the sign bit of the first live literal in a clause. -/
def firstLiteralSignConfig
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (literalBits restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (literalSign formulaValue clauseValue) blank
    (clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (literalBits.map ofBool ++ restLiteralPayload.map ofBool ++
      restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- Selection of the first live literal reaches its sign bit in three exact steps. -/
theorem run_clauseFind_to_firstLiteral
    (formulaValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (sign : Bool)
    (literalRest restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run 3
      (clauseFindFirstConfig formulaValue variableCount remainingClauses
        remainingLiterals
        ((sign :: literalRest) ++ restLiteralPayload)
        restPayload assignment suffix) =
    firstLiteralSignConfig formulaValue false variableCount
      remainingClauses remainingLiterals
      (sign :: literalRest) restLiteralPayload restPayload assignment suffix := by
  have h1 :
      satControl.run 1
        (clauseFindFirstConfig formulaValue variableCount remainingClauses
          remainingLiterals ((sign :: literalRest) ++ restLiteralPayload)
          restPayload assignment suffix) =
      configAt (clauseToCursor formulaValue false) blank
        (clauseSpent :: List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        (clauseEnd :: (sign :: literalRest).map ofBool ++
          restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
            List.replicate variableCount assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold clauseFindFirstConfig
    simp only [List.map_append, List.map_cons, List.cons_append]
    rw [step_clauseFind_live]
  have h2 :
      satControl.run 1
        (configAt (clauseToCursor formulaValue false) blank
          (clauseSpent :: List.replicate remainingLiterals clauseLive ++
            formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
              variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          (clauseEnd :: (sign :: literalRest).map ofBool ++
            restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
              List.replicate variableCount assignmentLengthChecked ++
                assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (clauseToCursor formulaValue false) blank
        (clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank])
        ((sign :: literalRest).map ofBool ++
          restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
            List.replicate variableCount assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_clauseToCursor_clauseEnd]
  have h3 :
      satControl.run 1
        (configAt (clauseToCursor formulaValue false) blank
          (clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
            formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
              variableEnd :: List.replicate variableCount variableChecked ++ [blank])
          ((sign :: literalRest).map ofBool ++
            restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
              List.replicate variableCount assignmentLengthChecked ++
                assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      firstLiteralSignConfig formulaValue false variableCount
        remainingClauses remainingLiterals
        (sign :: literalRest) restLiteralPayload restPayload assignment suffix := by
    rw [controlMachine_run_one]
    simp only [List.map_cons, List.cons_append]
    rw [step_clauseToCursor_raw]
    unfold firstLiteralSignConfig
    simp [List.append_assoc]
  rw [show 3 = 1 + (1 + 1) by omega]
  rw [controlMachine_run_add, h1]
  rw [controlMachine_run_add, h2]
  exact h3

end SATMachineCertificatePhase
end OpenProblems.Complexity
