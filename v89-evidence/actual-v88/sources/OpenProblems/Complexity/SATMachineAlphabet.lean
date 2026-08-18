import OpenProblems.Universal.TotalFiniteLowering

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

/-!
# Fixed finite control for the encoded-SAT verifier

This module fixes the alphabet, state numbering, and complete transition
architecture used by the later execution proofs.  It deliberately contains no
input-dependent states or transition tables.

The canonical verifier symbols retain their existing raw values:

* `0`: false;
* `1`: true;
* `2`: the input/certificate separator;
* `3`: blank.

The remaining symbols are private work markers.  Certificate assignment cells
have value-preserving false/true and visited-false/visited-true forms, so an
indexed lookup never loses the assignment as v65's single processed marker
did.

The control implements these phases:

1. decode and tag the certificate assignment prefix;
2. compare its declared length with the instance variable count;
3. decode nested formula/clause/literal prefixes;
4. perform a restoring zero-based assignment lookup;
5. fold literal values into clause OR and formula AND accumulators; and
6. accept only at the exact input separator frontier.

Every state/symbol pair not listed by a phase transition enters the absorbing
reject state.
-/

abbrev SATMachineSymbol := Fin 26

namespace SATMachineSymbol

def rawFalse : SATMachineSymbol := ⟨0, by decide⟩
def rawTrue : SATMachineSymbol := ⟨1, by decide⟩
def separator : SATMachineSymbol := ⟨2, by decide⟩
def blank : SATMachineSymbol := ⟨3, by decide⟩

def assignmentLengthLive : SATMachineSymbol := ⟨4, by decide⟩
def assignmentLengthSpent : SATMachineSymbol := ⟨5, by decide⟩
def assignmentLengthCount : SATMachineSymbol := ⟨6, by decide⟩
def assignmentLengthChecked : SATMachineSymbol := ⟨7, by decide⟩
def assignmentLengthEnd : SATMachineSymbol := ⟨8, by decide⟩

def assignmentFalse : SATMachineSymbol := ⟨9, by decide⟩
def assignmentTrue : SATMachineSymbol := ⟨10, by decide⟩
def assignmentVisitedFalse : SATMachineSymbol := ⟨11, by decide⟩
def assignmentVisitedTrue : SATMachineSymbol := ⟨12, by decide⟩

def variableLive : SATMachineSymbol := ⟨13, by decide⟩
def variableChecked : SATMachineSymbol := ⟨14, by decide⟩
def variableEnd : SATMachineSymbol := ⟨15, by decide⟩

def formulaLive : SATMachineSymbol := ⟨16, by decide⟩
def formulaSpent : SATMachineSymbol := ⟨17, by decide⟩
def formulaEnd : SATMachineSymbol := ⟨18, by decide⟩

def clauseLive : SATMachineSymbol := ⟨19, by decide⟩
def clauseSpent : SATMachineSymbol := ⟨20, by decide⟩
def clauseEnd : SATMachineSymbol := ⟨21, by decide⟩

def indexLive : SATMachineSymbol := ⟨22, by decide⟩
def indexSpent : SATMachineSymbol := ⟨23, by decide⟩
def indexEnd : SATMachineSymbol := ⟨24, by decide⟩

def processed : SATMachineSymbol := ⟨25, by decide⟩

@[simp] theorem rawFalse_val : rawFalse.val = 0 := rfl
@[simp] theorem rawTrue_val : rawTrue.val = 1 := rfl
@[simp] theorem separator_val : separator.val = 2 := rfl
@[simp] theorem blank_val : blank.val = 3 := rfl

def ofBool : Bool → SATMachineSymbol
  | false => rawFalse
  | true => rawTrue

@[simp]
theorem ofBool_val (bit : Bool) :
    (ofBool bit).val =
      match bit with
      | false => 0
      | true => 1 := by
  cases bit <;> rfl

end SATMachineSymbol

/-!
## State map

States `0` and `1` are the absorbing reject and accept states.  States `2`–`25`
are the outer scanner, certificate, count-comparison, and formula controller.

Four-state blocks use the order

`(formulaAcc, clauseAcc) = (F,F), (F,T), (T,F), (T,T)`.

Eight-state blocks use the order

`4 * formulaAcc + 2 * clauseAcc + flag`,

where `flag` is polarity (`false = negative`, `true = positive`) during
literal lookup, and the already polarity-adjusted literal value during
cleanup.

* `26..29`: find/decrement one clause marker;
* `30..33`: return to the next literal cursor;
* `34..37`: read a literal sign;
* `38..45`: decode its unary index;
* `46..53`: select an index marker;
* `54..61`: move right to the separator while skipping one assignment cell;
* `62..69`: skip one assignment cell;
* `70..77`: return from that skip to the index;
* `78..85`: move right to the target assignment cell;
* `86..93`: read the target/default value;
* `94..101`: restore the assignment and return to the index;
* `102..109`: erase index markers and update the clause accumulator.
-/

abbrev SATMachineState := Fin 110

namespace SATMachineState

def reject : SATMachineState := ⟨0, by decide⟩
def accept : SATMachineState := ⟨1, by decide⟩
def start : SATMachineState := ⟨2, by decide⟩
def seekSeparator : SATMachineState := ⟨3, by decide⟩
def certificateLength : SATMachineState := ⟨4, by decide⟩
def certificateFindLive : SATMachineState := ⟨5, by decide⟩
def certificateToPayload : SATMachineState := ⟨6, by decide⟩
def certificateNormalize : SATMachineState := ⟨7, by decide⟩
def returnLeft : SATMachineState := ⟨8, by decide⟩
def variableLength : SATMachineState := ⟨9, by decide⟩
def variableFindLive : SATMachineState := ⟨10, by decide⟩
def variableToSeparator : SATMachineState := ⟨11, by decide⟩
def variableFindAssignmentCount : SATMachineState := ⟨12, by decide⟩
def variableReturn : SATMachineState := ⟨13, by decide⟩
def variableFinishCheck : SATMachineState := ⟨14, by decide⟩
def variableCheckAssignment : SATMachineState := ⟨15, by decide⟩
def variableToFormula : SATMachineState := ⟨16, by decide⟩
def formulaLength : SATMachineState := ⟨17, by decide⟩

def formulaFind : Bool → SATMachineState
  | false => ⟨18, by decide⟩
  | true => ⟨19, by decide⟩

def formulaToCursor : Bool → SATMachineState
  | false => ⟨20, by decide⟩
  | true => ⟨21, by decide⟩

def formulaDoneToCursor : Bool → SATMachineState
  | false => ⟨22, by decide⟩
  | true => ⟨23, by decide⟩

def clauseLength : Bool → SATMachineState
  | false => ⟨24, by decide⟩
  | true => ⟨25, by decide⟩

def clauseFind : Bool → Bool → SATMachineState
  | false, false => ⟨26, by decide⟩
  | false, true => ⟨27, by decide⟩
  | true, false => ⟨28, by decide⟩
  | true, true => ⟨29, by decide⟩

def clauseToCursor : Bool → Bool → SATMachineState
  | false, false => ⟨30, by decide⟩
  | false, true => ⟨31, by decide⟩
  | true, false => ⟨32, by decide⟩
  | true, true => ⟨33, by decide⟩

def literalSign : Bool → Bool → SATMachineState
  | false, false => ⟨34, by decide⟩
  | false, true => ⟨35, by decide⟩
  | true, false => ⟨36, by decide⟩
  | true, true => ⟨37, by decide⟩

def indexRead : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨38, by decide⟩
  | false, false, true => ⟨39, by decide⟩
  | false, true, false => ⟨40, by decide⟩
  | false, true, true => ⟨41, by decide⟩
  | true, false, false => ⟨42, by decide⟩
  | true, false, true => ⟨43, by decide⟩
  | true, true, false => ⟨44, by decide⟩
  | true, true, true => ⟨45, by decide⟩

def lookupSelect : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨46, by decide⟩
  | false, false, true => ⟨47, by decide⟩
  | false, true, false => ⟨48, by decide⟩
  | false, true, true => ⟨49, by decide⟩
  | true, false, false => ⟨50, by decide⟩
  | true, false, true => ⟨51, by decide⟩
  | true, true, false => ⟨52, by decide⟩
  | true, true, true => ⟨53, by decide⟩

def lookupSkipRight : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨54, by decide⟩
  | false, false, true => ⟨55, by decide⟩
  | false, true, false => ⟨56, by decide⟩
  | false, true, true => ⟨57, by decide⟩
  | true, false, false => ⟨58, by decide⟩
  | true, false, true => ⟨59, by decide⟩
  | true, true, false => ⟨60, by decide⟩
  | true, true, true => ⟨61, by decide⟩

def lookupSkipCertificate : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨62, by decide⟩
  | false, false, true => ⟨63, by decide⟩
  | false, true, false => ⟨64, by decide⟩
  | false, true, true => ⟨65, by decide⟩
  | true, false, false => ⟨66, by decide⟩
  | true, false, true => ⟨67, by decide⟩
  | true, true, false => ⟨68, by decide⟩
  | true, true, true => ⟨69, by decide⟩

def lookupReturnIndex : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨70, by decide⟩
  | false, false, true => ⟨71, by decide⟩
  | false, true, false => ⟨72, by decide⟩
  | false, true, true => ⟨73, by decide⟩
  | true, false, false => ⟨74, by decide⟩
  | true, false, true => ⟨75, by decide⟩
  | true, true, false => ⟨76, by decide⟩
  | true, true, true => ⟨77, by decide⟩

def lookupTargetRight : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨78, by decide⟩
  | false, false, true => ⟨79, by decide⟩
  | false, true, false => ⟨80, by decide⟩
  | false, true, true => ⟨81, by decide⟩
  | true, false, false => ⟨82, by decide⟩
  | true, false, true => ⟨83, by decide⟩
  | true, true, false => ⟨84, by decide⟩
  | true, true, true => ⟨85, by decide⟩

def lookupTargetCertificate : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨86, by decide⟩
  | false, false, true => ⟨87, by decide⟩
  | false, true, false => ⟨88, by decide⟩
  | false, true, true => ⟨89, by decide⟩
  | true, false, false => ⟨90, by decide⟩
  | true, false, true => ⟨91, by decide⟩
  | true, true, false => ⟨92, by decide⟩
  | true, true, true => ⟨93, by decide⟩

def cleanupReturn : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨94, by decide⟩
  | false, false, true => ⟨95, by decide⟩
  | false, true, false => ⟨96, by decide⟩
  | false, true, true => ⟨97, by decide⟩
  | true, false, false => ⟨98, by decide⟩
  | true, false, true => ⟨99, by decide⟩
  | true, true, false => ⟨100, by decide⟩
  | true, true, true => ⟨101, by decide⟩

def cleanupIndex : Bool → Bool → Bool → SATMachineState
  | false, false, false => ⟨102, by decide⟩
  | false, false, true => ⟨103, by decide⟩
  | false, true, false => ⟨104, by decide⟩
  | false, true, true => ⟨105, by decide⟩
  | true, false, false => ⟨106, by decide⟩
  | true, false, true => ⟨107, by decide⟩
  | true, true, false => ⟨108, by decide⟩
  | true, true, true => ⟨109, by decide⟩

end SATMachineState

namespace SATMachineControl

open SATMachineSymbol
open SATMachineState

def action
    (next : SATMachineState)
    (write : SATMachineSymbol)
    (move : HeadMove) :
    ControlAction SATMachineState SATMachineSymbol :=
  {
    next := next
    write := write
    move := move
  }

def rejectAction
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  action reject symbol .stay

def keep
    (next : SATMachineState)
    (symbol : SATMachineSymbol)
    (move : HeadMove) :
    ControlAction SATMachineState SATMachineSymbol :=
  action next symbol move

def applyPolarity
    (positive value : Bool) :
    Bool :=
  if positive then value else !value

def formulaFindTransition
    (formulaValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 13 | 14 | 15 =>
      if symbol.val = 15 then
        keep (formulaDoneToCursor formulaValue) symbol .right
      else
        rejectAction symbol
  | 16 =>
      action (formulaToCursor formulaValue) formulaSpent .right
  | 17 | 18 | 19 | 20 | 21 | 25 =>
      keep (formulaFind formulaValue) symbol .left
  | _ =>
      rejectAction symbol

def formulaToCursorTransition
    (formulaValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 | 1 =>
      keep (clauseLength formulaValue) symbol .stay
  | 2 =>
      rejectAction symbol
  | 16 | 17 | 18 | 19 | 20 | 21 | 25 =>
      keep (formulaToCursor formulaValue) symbol .right
  | _ =>
      rejectAction symbol

def formulaDoneTransition
    (formulaValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 | 1 =>
      rejectAction symbol
  | 2 =>
      keep (if formulaValue then accept else reject)
        symbol .stay
  | 16 | 17 | 18 | 19 | 20 | 21 | 25 =>
      keep (formulaDoneToCursor formulaValue) symbol .right
  | _ =>
      rejectAction symbol

def clauseLengthTransition
    (formulaValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 =>
      action (clauseFind formulaValue false) clauseEnd .left
  | 1 =>
      action (clauseLength formulaValue) clauseLive .right
  | _ =>
      rejectAction symbol

def clauseFindTransition
    (formulaValue clauseValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 16 | 17 | 18 =>
      keep
        (formulaFind (formulaValue && clauseValue))
        symbol .left
  | 19 =>
      action
        (clauseToCursor formulaValue clauseValue)
        clauseSpent .right
  | 20 | 21 | 25 =>
      keep (clauseFind formulaValue clauseValue)
        symbol .left
  | _ =>
      rejectAction symbol

def clauseToCursorTransition
    (formulaValue clauseValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 | 1 =>
      keep (literalSign formulaValue clauseValue)
        symbol .stay
  | 2 =>
      rejectAction symbol
  | 19 | 20 | 21 | 25 =>
      keep (clauseToCursor formulaValue clauseValue)
        symbol .right
  | _ =>
      rejectAction symbol

def literalSignTransition
    (formulaValue clauseValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 =>
      action
        (indexRead formulaValue clauseValue false)
        processed .right
  | 1 =>
      action
        (indexRead formulaValue clauseValue true)
        processed .right
  | _ =>
      rejectAction symbol

def indexReadTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 0 =>
      action
        (lookupSelect formulaValue clauseValue positive)
        indexEnd .left
  | 1 =>
      action
        (indexRead formulaValue clauseValue positive)
        indexLive .right
  | _ =>
      rejectAction symbol

def lookupSelectTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 22 =>
      action
        (lookupSkipRight formulaValue clauseValue positive)
        indexSpent .right
  | 23 =>
      keep
        (lookupSelect formulaValue clauseValue positive)
        symbol .left
  | 25 =>
      keep
        (lookupTargetRight formulaValue clauseValue positive)
        symbol .right
  | _ =>
      rejectAction symbol

def lookupSkipRightTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 2 =>
      keep
        (lookupSkipCertificate
          formulaValue clauseValue positive)
        symbol .right
  | 0 | 1 | 16 | 17 | 18 | 19 | 20 | 21
  | 22 | 23 | 24 | 25 =>
      keep
        (lookupSkipRight formulaValue clauseValue positive)
        symbol .right
  | _ =>
      rejectAction symbol

def lookupSkipCertificateTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 7 | 8 | 11 | 12 =>
      keep
        (lookupSkipCertificate
          formulaValue clauseValue positive)
        symbol .right
  | 9 =>
      action
        (lookupReturnIndex
          formulaValue clauseValue positive)
        assignmentVisitedFalse .left
  | 10 =>
      action
        (lookupReturnIndex
          formulaValue clauseValue positive)
        assignmentVisitedTrue .left
  | 0 | 1 | 3 =>
      keep
        (cleanupReturn formulaValue clauseValue
          (applyPolarity positive false))
        symbol .left
  | _ =>
      rejectAction symbol

def lookupReturnIndexTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 24 =>
      keep
        (lookupSelect formulaValue clauseValue positive)
        symbol .left
  | 0 | 1 | 2 | 7 | 8 | 9 | 10 | 11 | 12
  | 16 | 17 | 18 | 19 | 20 | 21 | 25 =>
      keep
        (lookupReturnIndex
          formulaValue clauseValue positive)
        symbol .left
  | _ =>
      rejectAction symbol

def lookupTargetRightTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 2 =>
      keep
        (lookupTargetCertificate
          formulaValue clauseValue positive)
        symbol .right
  | 0 | 1 | 16 | 17 | 18 | 19 | 20 | 21
  | 22 | 23 | 24 | 25 =>
      keep
        (lookupTargetRight
          formulaValue clauseValue positive)
        symbol .right
  | _ =>
      rejectAction symbol

def lookupTargetCertificateTransition
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 7 | 8 | 11 | 12 =>
      keep
        (lookupTargetCertificate
          formulaValue clauseValue positive)
        symbol .right
  | 9 =>
      keep
        (cleanupReturn formulaValue clauseValue
          (applyPolarity positive false))
        symbol .left
  | 10 =>
      keep
        (cleanupReturn formulaValue clauseValue
          (applyPolarity positive true))
        symbol .left
  | 0 | 1 | 3 =>
      keep
        (cleanupReturn formulaValue clauseValue
          (applyPolarity positive false))
        symbol .left
  | _ =>
      rejectAction symbol

def cleanupReturnTransition
    (formulaValue clauseValue literalValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 11 =>
      action
        (cleanupReturn
          formulaValue clauseValue literalValue)
        assignmentFalse .left
  | 12 =>
      action
        (cleanupReturn
          formulaValue clauseValue literalValue)
        assignmentTrue .left
  | 24 =>
      action
        (cleanupIndex
          formulaValue clauseValue literalValue)
        processed .left
  | 0 | 1 | 2 | 7 | 8 | 9 | 10
  | 16 | 17 | 18 | 19 | 20 | 21 | 25 =>
      keep
        (cleanupReturn
          formulaValue clauseValue literalValue)
        symbol .left
  | _ =>
      rejectAction symbol

def cleanupIndexTransition
    (formulaValue clauseValue literalValue : Bool)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match symbol.val with
  | 22 | 23 =>
      action
        (cleanupIndex
          formulaValue clauseValue literalValue)
        processed .left
  | 25 =>
      keep
        (clauseFind formulaValue
          (clauseValue || literalValue))
        symbol .left
  | _ =>
      rejectAction symbol

def transition
    (state : SATMachineState)
    (symbol : SATMachineSymbol) :
    ControlAction SATMachineState SATMachineSymbol :=
  match state.val with
  | 0 =>
      keep reject symbol .stay
  | 1 =>
      keep accept symbol .stay
  | 2 =>
      if symbol.val = 3 then
        keep seekSeparator symbol .right
      else
        rejectAction symbol
  | 3 =>
      match symbol.val with
      | 0 | 1 =>
          keep seekSeparator symbol .right
      | 2 =>
          keep certificateLength symbol .right
      | _ =>
          rejectAction symbol
  | 4 =>
      match symbol.val with
      | 0 =>
          action certificateFindLive
            assignmentLengthEnd .left
      | 1 =>
          action certificateLength
            assignmentLengthLive .right
      | _ =>
          rejectAction symbol
  | 5 =>
      match symbol.val with
      | 2 =>
          keep certificateNormalize symbol .right
      | 4 =>
          action certificateToPayload
            assignmentLengthSpent .right
      | 5 | 8 | 9 | 10 =>
          keep certificateFindLive symbol .left
      | _ =>
          rejectAction symbol
  | 6 =>
      match symbol.val with
      | 0 =>
          action certificateFindLive
            assignmentFalse .left
      | 1 =>
          action certificateFindLive
            assignmentTrue .left
      | 5 | 8 | 9 | 10 =>
          keep certificateToPayload symbol .right
      | _ =>
          rejectAction symbol
  | 7 =>
      match symbol.val with
      | 5 =>
          action certificateNormalize
            assignmentLengthCount .right
      | 8 =>
          keep returnLeft symbol .left
      | _ =>
          rejectAction symbol
  | 8 =>
      match symbol.val with
      | 3 =>
          keep variableLength symbol .right
      | 0 | 1 | 2 | 6 | 7 | 8 =>
          keep returnLeft symbol .left
      | _ =>
          rejectAction symbol
  | 9 =>
      match symbol.val with
      | 0 =>
          action variableFindLive variableEnd .left
      | 1 =>
          action variableLength variableLive .right
      | _ =>
          rejectAction symbol
  | 10 =>
      match symbol.val with
      | 3 =>
          keep variableFinishCheck symbol .right
      | 13 =>
          action variableToSeparator variableChecked .right
      | 14 =>
          keep variableFindLive symbol .left
      | _ =>
          rejectAction symbol
  | 11 =>
      match symbol.val with
      | 2 =>
          keep variableFindAssignmentCount symbol .right
      | 0 | 1 | 13 | 14 | 15 =>
          keep variableToSeparator symbol .right
      | _ =>
          rejectAction symbol
  | 12 =>
      match symbol.val with
      | 6 =>
          action variableReturn
            assignmentLengthChecked .left
      | 7 =>
          keep variableFindAssignmentCount symbol .right
      | 8 =>
          rejectAction symbol
      | _ =>
          rejectAction symbol
  | 13 =>
      match symbol.val with
      | 15 =>
          keep variableFindLive symbol .left
      | 0 | 1 | 2 | 6 | 7 | 8 | 13 | 14 =>
          keep variableReturn symbol .left
      | _ =>
          rejectAction symbol
  | 14 =>
      match symbol.val with
      | 2 =>
          keep variableCheckAssignment symbol .right
      | 0 | 1 | 13 | 14 | 15 =>
          keep variableFinishCheck symbol .right
      | _ =>
          rejectAction symbol
  | 15 =>
      match symbol.val with
      | 6 =>
          rejectAction symbol
      | 7 =>
          keep variableCheckAssignment symbol .right
      | 8 =>
          keep variableToFormula symbol .left
      | _ =>
          rejectAction symbol
  | 16 =>
      match symbol.val with
      | 15 =>
          keep formulaLength symbol .right
      | 0 | 1 | 2 | 7 | 8 =>
          keep variableToFormula symbol .left
      | _ =>
          rejectAction symbol
  | 17 =>
      match symbol.val with
      | 0 =>
          action (formulaFind true) formulaEnd .left
      | 1 =>
          action formulaLength formulaLive .right
      | _ =>
          rejectAction symbol
  | 18 =>
      formulaFindTransition false symbol
  | 19 =>
      formulaFindTransition true symbol
  | 20 =>
      formulaToCursorTransition false symbol
  | 21 =>
      formulaToCursorTransition true symbol
  | 22 =>
      formulaDoneTransition false symbol
  | 23 =>
      formulaDoneTransition true symbol
  | 24 =>
      clauseLengthTransition false symbol
  | 25 =>
      clauseLengthTransition true symbol
  | 26 =>
      clauseFindTransition false false symbol
  | 27 =>
      clauseFindTransition false true symbol
  | 28 =>
      clauseFindTransition true false symbol
  | 29 =>
      clauseFindTransition true true symbol
  | 30 =>
      clauseToCursorTransition false false symbol
  | 31 =>
      clauseToCursorTransition false true symbol
  | 32 =>
      clauseToCursorTransition true false symbol
  | 33 =>
      clauseToCursorTransition true true symbol
  | 34 =>
      literalSignTransition false false symbol
  | 35 =>
      literalSignTransition false true symbol
  | 36 =>
      literalSignTransition true false symbol
  | 37 =>
      literalSignTransition true true symbol
  | 38 =>
      indexReadTransition false false false symbol
  | 39 =>
      indexReadTransition false false true symbol
  | 40 =>
      indexReadTransition false true false symbol
  | 41 =>
      indexReadTransition false true true symbol
  | 42 =>
      indexReadTransition true false false symbol
  | 43 =>
      indexReadTransition true false true symbol
  | 44 =>
      indexReadTransition true true false symbol
  | 45 =>
      indexReadTransition true true true symbol
  | 46 =>
      lookupSelectTransition false false false symbol
  | 47 =>
      lookupSelectTransition false false true symbol
  | 48 =>
      lookupSelectTransition false true false symbol
  | 49 =>
      lookupSelectTransition false true true symbol
  | 50 =>
      lookupSelectTransition true false false symbol
  | 51 =>
      lookupSelectTransition true false true symbol
  | 52 =>
      lookupSelectTransition true true false symbol
  | 53 =>
      lookupSelectTransition true true true symbol
  | 54 =>
      lookupSkipRightTransition false false false symbol
  | 55 =>
      lookupSkipRightTransition false false true symbol
  | 56 =>
      lookupSkipRightTransition false true false symbol
  | 57 =>
      lookupSkipRightTransition false true true symbol
  | 58 =>
      lookupSkipRightTransition true false false symbol
  | 59 =>
      lookupSkipRightTransition true false true symbol
  | 60 =>
      lookupSkipRightTransition true true false symbol
  | 61 =>
      lookupSkipRightTransition true true true symbol
  | 62 =>
      lookupSkipCertificateTransition false false false symbol
  | 63 =>
      lookupSkipCertificateTransition false false true symbol
  | 64 =>
      lookupSkipCertificateTransition false true false symbol
  | 65 =>
      lookupSkipCertificateTransition false true true symbol
  | 66 =>
      lookupSkipCertificateTransition true false false symbol
  | 67 =>
      lookupSkipCertificateTransition true false true symbol
  | 68 =>
      lookupSkipCertificateTransition true true false symbol
  | 69 =>
      lookupSkipCertificateTransition true true true symbol
  | 70 =>
      lookupReturnIndexTransition false false false symbol
  | 71 =>
      lookupReturnIndexTransition false false true symbol
  | 72 =>
      lookupReturnIndexTransition false true false symbol
  | 73 =>
      lookupReturnIndexTransition false true true symbol
  | 74 =>
      lookupReturnIndexTransition true false false symbol
  | 75 =>
      lookupReturnIndexTransition true false true symbol
  | 76 =>
      lookupReturnIndexTransition true true false symbol
  | 77 =>
      lookupReturnIndexTransition true true true symbol
  | 78 =>
      lookupTargetRightTransition false false false symbol
  | 79 =>
      lookupTargetRightTransition false false true symbol
  | 80 =>
      lookupTargetRightTransition false true false symbol
  | 81 =>
      lookupTargetRightTransition false true true symbol
  | 82 =>
      lookupTargetRightTransition true false false symbol
  | 83 =>
      lookupTargetRightTransition true false true symbol
  | 84 =>
      lookupTargetRightTransition true true false symbol
  | 85 =>
      lookupTargetRightTransition true true true symbol
  | 86 =>
      lookupTargetCertificateTransition false false false symbol
  | 87 =>
      lookupTargetCertificateTransition false false true symbol
  | 88 =>
      lookupTargetCertificateTransition false true false symbol
  | 89 =>
      lookupTargetCertificateTransition false true true symbol
  | 90 =>
      lookupTargetCertificateTransition true false false symbol
  | 91 =>
      lookupTargetCertificateTransition true false true symbol
  | 92 =>
      lookupTargetCertificateTransition true true false symbol
  | 93 =>
      lookupTargetCertificateTransition true true true symbol
  | 94 =>
      cleanupReturnTransition false false false symbol
  | 95 =>
      cleanupReturnTransition false false true symbol
  | 96 =>
      cleanupReturnTransition false true false symbol
  | 97 =>
      cleanupReturnTransition false true true symbol
  | 98 =>
      cleanupReturnTransition true false false symbol
  | 99 =>
      cleanupReturnTransition true false true symbol
  | 100 =>
      cleanupReturnTransition true true false symbol
  | 101 =>
      cleanupReturnTransition true true true symbol
  | 102 =>
      cleanupIndexTransition false false false symbol
  | 103 =>
      cleanupIndexTransition false false true symbol
  | 104 =>
      cleanupIndexTransition false true false symbol
  | 105 =>
      cleanupIndexTransition false true true symbol
  | 106 =>
      cleanupIndexTransition true false false symbol
  | 107 =>
      cleanupIndexTransition true false true symbol
  | 108 =>
      cleanupIndexTransition true true false symbol
  | 109 =>
      cleanupIndexTransition true true true symbol
  | _ =>
      rejectAction symbol

end SATMachineControl

open SATMachineControl

/-- One fixed typed control machine for all encoded-SAT inputs and witnesses. -/
def encodedSATFiniteControl : FiniteControlMachine where
  stateCount := 110
  symbolCount := 26
  stateCount_pos := by decide
  symbolCount_pos := by decide
  control :=
    {
      blank := SATMachineSymbol.blank
      start := SATMachineState.start
      halt := fun state =>
        decide
          (state = SATMachineState.reject ∨
            state = SATMachineState.accept)
      accept := fun state =>
        decide (state = SATMachineState.accept)
      transition := SATMachineControl.transition
      accept_halts := by
        intro state haccept
        simp only [decide_eq_true_eq] at haccept ⊢
        exact Or.inr haccept
    }

/-- Trusted raw transition-table lowering of the fixed typed SAT control. -/
def encodedSATFiniteMachine : FiniteMachine :=
  encodedSATFiniteControl.lowerAbsorbing

@[simp]
theorem encodedSATFiniteMachine_stateCount :
    encodedSATFiniteMachine.code.stateCount = 110 :=
  rfl

@[simp]
theorem encodedSATFiniteMachine_symbolCount :
    encodedSATFiniteMachine.code.symbolCount = 26 :=
  rfl

@[simp]
theorem encodedSATFiniteMachine_blank :
    encodedSATFiniteMachine.code.blank = 3 :=
  rfl

@[simp]
theorem encodedSATFiniteMachine_start :
    encodedSATFiniteMachine.code.start = 2 :=
  rfl

theorem encodedSATFiniteMachine_wellFormed :
    encodedSATFiniteMachine.code.WellFormed :=
  encodedSATFiniteMachine.valid

/-- The fixed work alphabet contains the canonical `0`, `1`, `2` payload. -/
theorem encodedSATFiniteMachine_symbolCapacity :
    3 ≤ encodedSATFiniteMachine.code.symbolCount := by
  decide

@[simp]
theorem encodedSATFiniteControl_halt_reject :
    encodedSATFiniteControl.control.halt
        SATMachineState.reject =
      true := by
  simp [encodedSATFiniteControl, SATMachineState.reject,
    SATMachineState.accept]

@[simp]
theorem encodedSATFiniteControl_halt_accept :
    encodedSATFiniteControl.control.halt
        SATMachineState.accept =
      true := by
  simp [encodedSATFiniteControl, SATMachineState.reject,
    SATMachineState.accept]

@[simp]
theorem encodedSATFiniteControl_accept_reject :
    encodedSATFiniteControl.control.accept
        SATMachineState.reject =
      false := by
  simp [encodedSATFiniteControl, SATMachineState.reject,
    SATMachineState.accept]

@[simp]
theorem encodedSATFiniteControl_accept_accept :
    encodedSATFiniteControl.control.accept
        SATMachineState.accept =
      true := by
  simp [encodedSATFiniteControl, SATMachineState.accept]

/-- Typed rejection is absorbing for every later execution budget. -/
theorem encodedSATFiniteControl_run_reject
    (steps : Nat)
    (tape : Tape SATMachineSymbol) :
    encodedSATFiniteControl.control.run steps
        {
          state := SATMachineState.reject
          tape := tape
        } =
      {
        state := SATMachineState.reject
        tape := tape
      } := by
  exact
    ControlMachine.run_of_halted
      encodedSATFiniteControl.control
      steps
      {
        state := SATMachineState.reject
        tape := tape
      }
      encodedSATFiniteControl_halt_reject

/-- Typed acceptance is absorbing for every later execution budget. -/
theorem encodedSATFiniteControl_run_accept
    (steps : Nat)
    (tape : Tape SATMachineSymbol) :
    encodedSATFiniteControl.control.run steps
        {
          state := SATMachineState.accept
          tape := tape
        } =
      {
        state := SATMachineState.accept
        tape := tape
      } := by
  exact
    ControlMachine.run_of_halted
      encodedSATFiniteControl.control
      steps
      {
        state := SATMachineState.accept
        tape := tape
      }
      encodedSATFiniteControl_halt_accept

/-- Raw lowered rejection is absorbing on every encoded typed tape. -/
theorem encodedSATFiniteMachine_run_reject
    (steps : Nat)
    (tape : Tape SATMachineSymbol) :
    encodedSATFiniteMachine.toDTM.run steps
        (FiniteControlMachine.encodeConfig
          {
            state := SATMachineState.reject
            tape := tape
          }) =
      FiniteControlMachine.encodeConfig
        {
          state := SATMachineState.reject
          tape := tape
        } := by
  unfold encodedSATFiniteMachine
  calc
    _ = FiniteControlMachine.encodeConfig
        (encodedSATFiniteControl.control.run steps
          { state := SATMachineState.reject, tape := tape }) :=
      FiniteControlMachine.lowerAbsorbing_run_commutes
        encodedSATFiniteControl steps
        { state := SATMachineState.reject, tape := tape }
    _ = _ := congrArg FiniteControlMachine.encodeConfig
      (encodedSATFiniteControl_run_reject steps tape)

/-- Raw lowered acceptance is absorbing on every encoded typed tape. -/
theorem encodedSATFiniteMachine_run_accept
    (steps : Nat)
    (tape : Tape SATMachineSymbol) :
    encodedSATFiniteMachine.toDTM.run steps
        (FiniteControlMachine.encodeConfig
          {
            state := SATMachineState.accept
            tape := tape
          }) =
      FiniteControlMachine.encodeConfig
        {
          state := SATMachineState.accept
          tape := tape
        } := by
  unfold encodedSATFiniteMachine
  calc
    _ = FiniteControlMachine.encodeConfig
        (encodedSATFiniteControl.control.run steps
          { state := SATMachineState.accept, tape := tape }) :=
      FiniteControlMachine.lowerAbsorbing_run_commutes
        encodedSATFiniteControl steps
        { state := SATMachineState.accept, tape := tape }
    _ = _ := congrArg FiniteControlMachine.encodeConfig
      (encodedSATFiniteControl_run_accept steps tape)

end OpenProblems.Complexity
