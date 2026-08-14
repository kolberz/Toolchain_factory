import Std.Tactic.Omega

namespace V89Harness

inductive Sym where
  | rawFalse | rawTrue | blank
  | formulaLive | formulaSpent | formulaEnd
  | clauseLive | clauseSpent | clauseEnd | processed
  deriving DecidableEq, Repr

inductive State where
  | reject
  | clauseFind (formulaValue clauseValue : Bool)
  | clauseToCursor (formulaValue clauseValue : Bool)
  | literalSign (formulaValue clauseValue : Bool)
  deriving DecidableEq, Repr

inductive Move where | left | right | stay
  deriving DecidableEq, Repr

structure Action where
  next : State
  write : Sym
  move : Move
  deriving Repr

structure Tape where
  left : List Sym
  head : Sym
  right : List Sym
  deriving Repr, DecidableEq

structure Config where
  state : State
  tape : Tape
  deriving Repr, DecidableEq

open Sym State Move


def configAt (state : State) (left payload : List Sym) : Config :=
  match payload with
  | [] => { state := state, tape := { left := left, head := blank, right := [] } }
  | head :: right => { state := state, tape := { left := left, head := head, right := right } }


def transition (state : State) (symbol : Sym) : Action :=
  match state with
  | .reject => { next := .reject, write := symbol, move := .stay }
  | .literalSign _ _ => { next := .reject, write := symbol, move := .stay }
  | .clauseFind f c =>
      match symbol with
      | .formulaLive | .formulaSpent | .formulaEnd =>
          { next := .reject, write := symbol, move := .left }
      | .clauseLive =>
          { next := .clauseToCursor f c, write := .clauseSpent, move := .right }
      | .clauseSpent | .clauseEnd | .processed =>
          { next := .clauseFind f c, write := symbol, move := .left }
      | _ => { next := .reject, write := symbol, move := .stay }
  | .clauseToCursor f c =>
      match symbol with
      | .rawFalse | .rawTrue =>
          { next := .literalSign f c, write := symbol, move := .stay }
      | .clauseLive | .clauseSpent | .clauseEnd | .processed =>
          { next := .clauseToCursor f c, write := symbol, move := .right }
      | _ => { next := .reject, write := symbol, move := .stay }


def stepConfig (config : Config) : Config :=
  let action := transition config.state config.tape.head
  match action.move with
  | .stay =>
      { state := action.next,
        tape := { config.tape with head := action.write } }
  | .right =>
      match config.tape.right with
      | [] =>
          { state := action.next,
            tape := { left := action.write :: config.tape.left,
                      head := blank, right := [] } }
      | head :: right =>
          { state := action.next,
            tape := { left := action.write :: config.tape.left,
                      head := head, right := right } }
  | .left =>
      match config.tape.left with
      | [] =>
          { state := action.next,
            tape := { left := [], head := blank,
                      right := action.write :: config.tape.right } }
      | head :: left =>
          { state := action.next,
            tape := { left := left, head := head,
                      right := action.write :: config.tape.right } }


def run : Nat → Config → Config
  | 0, config => config
  | n + 1, config => run n (stepConfig config)


theorem run_add (m n : Nat) (config : Config) :
    run (m + n) config = run n (run m config) := by
  induction m generalizing config with
  | zero => rfl
  | succ m ih =>
      simp only [Nat.succ_eq_add_one, Nat.add_assoc]
      change run (m + n + 1) config = _
      rw [show m + n + 1 = (m + 1) + n by omega]
      change run n (run (m + 1) config) = _
      rfl


theorem run_one (config : Config) : run 1 config = stepConfig config := rfl


def keepLeftScanConfig
    (q : State) (markers : List Sym) (baseHead : Sym)
    (baseLeft right : List Sym) : Config :=
  match markers with
  | [] => configAt q baseLeft (baseHead :: right)
  | marker :: remaining =>
      configAt q (remaining ++ baseHead :: baseLeft) (marker :: right)


theorem run_keepLeft_markers
    (q : State) (P : Sym → Prop) (markers : List Sym)
    (baseHead : Sym) (baseLeft right : List Sym)
    (hstep : ∀ marker, P marker → ∀ leftHead leftTail r,
      stepConfig (configAt q (leftHead :: leftTail) (marker :: r)) =
        configAt q leftTail (leftHead :: marker :: r))
    (hmarkers : ∀ marker ∈ markers, P marker) :
    run markers.length (keepLeftScanConfig q markers baseHead baseLeft right) =
      configAt q baseLeft (baseHead :: markers.reverse ++ right) := by
  induction markers generalizing right with
  | nil => rfl
  | cons marker markers ih =>
      change run (markers.length + 1)
        (configAt q (markers ++ baseHead :: baseLeft) (marker :: right)) = _
      change run markers.length
        (stepConfig (configAt q (markers ++ baseHead :: baseLeft) (marker :: right))) = _
      have hm : P marker := hmarkers marker (by simp)
      cases markers with
      | nil =>
          simp only [List.nil_append]
          rw [hstep marker hm baseHead baseLeft right]
          rfl
      | cons next rest =>
          rw [List.cons_append]
          rw [hstep marker hm next (rest ++ baseHead :: baseLeft) right]
          have htail : ∀ m ∈ (next :: rest), P m := by
            intro m hmem
            exact hmarkers m (by simp [hmem])
          have hrec := ih (right := marker :: right) htail
          exact hrec


theorem run_keepRight_markers
    (q : State) (P : Sym → Prop) (markers : List Sym)
    (left payload : List Sym)
    (hstep : ∀ marker, P marker → ∀ l r,
      stepConfig (configAt q l (marker :: r)) =
        configAt q (marker :: l) r)
    (hmarkers : ∀ marker ∈ markers, P marker) :
    run markers.length (configAt q left (markers ++ payload)) =
      configAt q (markers.reverse ++ left) payload := by
  induction markers generalizing left with
  | nil => rfl
  | cons marker markers ih =>
      rw [List.cons_append]
      change run markers.length
        (stepConfig (configAt q left (marker :: (markers ++ payload)))) = _
      rw [hstep marker (hmarkers marker (by simp)) left (markers ++ payload)]
      have htail : ∀ m ∈ markers, P m := by
        intro m hm
        exact hmarkers m (by simp [hm])
      rw [ih (left := marker :: left) htail]
      simp [List.reverse_cons, List.append_assoc]


@[simp] theorem step_clauseFind_clauseEnd
    (f c : Bool) (leftHead : Sym) (leftTail right : List Sym) :
    stepConfig (configAt (.clauseFind f c) (leftHead :: leftTail) (.clauseEnd :: right)) =
      configAt (.clauseFind f c) leftTail (leftHead :: .clauseEnd :: right) := by
  rfl

@[simp] theorem step_clauseFind_spent
    (f c : Bool) (leftHead : Sym) (leftTail right : List Sym) :
    stepConfig (configAt (.clauseFind f c) (leftHead :: leftTail) (.clauseSpent :: right)) =
      configAt (.clauseFind f c) leftTail (leftHead :: .clauseSpent :: right) := by
  rfl

@[simp] theorem step_clauseFind_live
    (f c : Bool) (left right : List Sym) :
    stepConfig (configAt (.clauseFind f c) left (.clauseLive :: right)) =
      configAt (.clauseToCursor f c) (.clauseSpent :: left) right := by
  rfl


def cursorMarker (symbol : Sym) : Prop :=
  symbol = .clauseSpent ∨ symbol = .clauseEnd ∨ symbol = .processed

@[simp] theorem step_clauseToCursor_marker
    (f c : Bool) (symbol : Sym) (h : cursorMarker symbol)
    (left right : List Sym) :
    stepConfig (configAt (.clauseToCursor f c) left (symbol :: right)) =
      configAt (.clauseToCursor f c) (symbol :: left) right := by
  rcases h with rfl | rfl | rfl <;> rfl

@[simp] theorem step_clauseToCursor_raw
    (f c sign : Bool) (left right : List Sym) :
    stepConfig (configAt (.clauseToCursor f c) left
      ((if sign then .rawTrue else .rawFalse) :: right)) =
      configAt (.literalSign f c) left
        ((if sign then .rawTrue else .rawFalse) :: right) := by
  cases sign <;> rfl


def historyFind
    (f c : Bool) (j k p : Nat) (sign : Bool)
    (literalRest outerLeft tail : List Sym) : Config :=
  configAt (.clauseFind f c)
    (List.replicate j .clauseSpent ++
      List.replicate (k + 1) .clauseLive ++ outerLeft)
    (.clauseEnd :: List.replicate p .processed ++
      (if sign then .rawTrue else .rawFalse) :: literalRest ++ tail)


def historySign
    (f c : Bool) (j k p : Nat) (sign : Bool)
    (literalRest outerLeft tail : List Sym) : Config :=
  configAt (.literalSign f c)
    (List.replicate p .processed ++ .clauseEnd ::
      List.replicate (j + 1) .clauseSpent ++
        List.replicate k .clauseLive ++ outerLeft)
    ((if sign then .rawTrue else .rawFalse) :: literalRest ++ tail)


theorem run_historyFind_to_sign
    (f c sign : Bool) (j k p : Nat)
    (literalRest outerLeft tail : List Sym) :
    run (p + 2*j + 4) (historyFind f c j k p sign literalRest outerLeft tail) =
      historySign f c j k p sign literalRest outerLeft tail := by
  let baseLeft := List.replicate k .clauseLive ++ outerLeft
  let literalRight := (if sign then .rawTrue else .rawFalse) :: literalRest ++ tail
  let spentMarkers := List.replicate j .clauseSpent
  let cursorMarkers := spentMarkers ++ .clauseEnd :: List.replicate p .processed
  have hfirst :
      run 1 (historyFind f c j k p sign literalRest outerLeft tail) =
      keepLeftScanConfig (.clauseFind f c) spentMarkers .clauseLive baseLeft
        (.clauseEnd :: List.replicate p .processed ++ literalRight) := by
    rw [run_one]
    unfold historyFind spentMarkers baseLeft literalRight
    cases j with
    | zero => simp [keepLeftScanConfig, List.append_assoc]
    | succ n =>
        rw [List.replicate_succ]
        simp only [List.cons_append]
        rw [step_clauseFind_clauseEnd]
        simp [keepLeftScanConfig, List.append_assoc]
  have hspent := run_keepLeft_markers
    (.clauseFind f c) (fun s => s = .clauseSpent)
    spentMarkers .clauseLive baseLeft
    (.clauseEnd :: List.replicate p .processed ++ literalRight)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_clauseFind_spent f c leftHead leftTail right)
    (by
      intro marker hm
      unfold spentMarkers at hm
      exact List.eq_of_mem_replicate hm)
  have hspent' :
      run j (keepLeftScanConfig (.clauseFind f c) spentMarkers .clauseLive baseLeft
        (.clauseEnd :: List.replicate p .processed ++ literalRight)) =
      configAt (.clauseFind f c) baseLeft
        (.clauseLive :: spentMarkers.reverse ++ .clauseEnd ::
          List.replicate p .processed ++ literalRight) := by
    simpa [spentMarkers] using hspent
  have hlive :
      run 1 (configAt (.clauseFind f c) baseLeft
        (.clauseLive :: spentMarkers.reverse ++ .clauseEnd ::
          List.replicate p .processed ++ literalRight)) =
      configAt (.clauseToCursor f c) (.clauseSpent :: baseLeft)
        (cursorMarkers ++ literalRight) := by
    rw [run_one, step_clauseFind_live]
    unfold cursorMarkers spentMarkers
    simp [List.append_assoc]
  have hcursorAll : ∀ marker ∈ cursorMarkers, cursorMarker marker := by
    intro marker hm
    unfold cursorMarkers spentMarkers at hm
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hm
    rcases hm with hspentMem | hend | hprocessed
    · exact Or.inl hspentMem.2
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr hprocessed.2)
  have hcursor := run_keepRight_markers
    (.clauseToCursor f c) cursorMarker cursorMarkers
    (.clauseSpent :: baseLeft) literalRight
    (step_clauseToCursor_marker f c) hcursorAll
  have hcursor' :
      run (j + 1 + p)
        (configAt (.clauseToCursor f c) (.clauseSpent :: baseLeft)
          (cursorMarkers ++ literalRight)) =
      configAt (.clauseToCursor f c)
        (List.replicate p .processed ++ .clauseEnd ::
          List.replicate (j + 1) .clauseSpent ++ baseLeft)
        literalRight := by
    have hlen : cursorMarkers.length = j + 1 + p := by
      unfold cursorMarkers spentMarkers
      simp
    rw [← hlen, hcursor]
    unfold cursorMarkers spentMarkers baseLeft literalRight
    simp [List.reverse_append, List.replicate_succ, List.append_assoc]
  have hraw :
      run 1 (configAt (.clauseToCursor f c)
        (List.replicate p .processed ++ .clauseEnd ::
          List.replicate (j + 1) .clauseSpent ++ baseLeft) literalRight) =
      historySign f c j k p sign literalRest outerLeft tail := by
    rw [run_one]
    unfold literalRight
    rw [step_clauseToCursor_raw]
    unfold historySign baseLeft
    simp [List.append_assoc]
  rw [show p + 2*j + 4 = 1 + (j + (1 + ((j + 1 + p) + 1))) by omega]
  rw [run_add, hfirst]
  rw [run_add, hspent']
  rw [run_add, hlive]
  rw [run_add, hcursor']
  exact hraw

#print axioms run_historyFind_to_sign

end V89Harness
