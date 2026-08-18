import OpenProblems.Complexity.SATMachineLookupPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- Concrete suffix representation after an assignment-exhaustion transition.
When the logical suffix is empty, moving left from the implicit blank
materializes one explicit blank cell on the right side of the zipper. -/
def defaultSuffixSymbols (suffix : BitString) : List SATMachineSymbol :=
  match suffix with
  | [] => [blank]
  | _ => suffix.map ofBool

@[simp] theorem defaultSuffixSymbols_nil :
    defaultSuffixSymbols [] = [blank] := rfl

@[simp] theorem defaultSuffixSymbols_cons (bit : Bool) (rest : BitString) :
    defaultSuffixSymbols (bit :: rest) = ofBool bit :: rest.map ofBool := rfl

/-- Canonical result of an out-of-range lookup after every assignment slot has
been visited. The missing assignment value is interpreted as `false`, matching
`CNF.valueAt`. -/
def defaultLiteralEvaluatedConfig
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
            defaultSuffixSymbols suffix)

/-- Assignment exhaustion exactly at the requested index. All assignment cells
are restored and the missing target value is interpreted as `false`. -/
theorem run_lookupLoop_default_zero
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited restLiteralPayload restPayload suffix : BitString) :
    satControl.run
      (4 * visited.length + 2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + 9)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited 0
        restLiteralPayload restPayload [] suffix) =
    defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals visited 0 restLiteralPayload restPayload
      suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hselect :
      satControl.run 1
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited 0
          restLiteralPayload restPayload [] suffix) =
      configAt (lookupTargetRight formulaValue clauseValue positive) blank
        (processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ suffix.map ofBool)) := by
    rw [controlMachine_run_one]
    unfold lookupLoopConfig baseLeft rightMarkers certMarkers
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    cases formulaValue <;> cases clauseValue <;> cases positive <;>
      simp [List.append_assoc]
    all_goals rfl
  have hright := run_keepRight_markers
    (lookupTargetRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers (processed :: baseLeft)
    (separator :: certMarkers ++ suffix.map ofBool)
    (step_lookupTargetRight_lookupMarker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupTargetRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ processed :: baseLeft)
          (separator :: certMarkers ++ suffix.map ofBool)) =
      configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ processed :: baseLeft)
        (certMarkers ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    exact step_lookupTargetRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupTargetCertificate formulaValue clauseValue positive)
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ processed :: baseLeft)
    (suffix.map ofBool)
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
  have hdefault :
      satControl.run 1
        (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft))
          (suffix.map ofBool)) =
      keepLeftScanConfig
        (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
        returnMarkers indexEnd
        (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        (defaultSuffixSymbols suffix) := by
    rw [hleftLayout]
    cases suffix with
    | nil =>
        unfold defaultSuffixSymbols
        cases hret : returnMarkers with
        | nil => exact (hreturnMarkers_ne hret).elim
        | cons marker remaining =>
            simp only [List.cons_append]
            rw [controlMachine_run_one]
            cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
    | cons bit rest =>
        unfold defaultSuffixSymbols
        cases hret : returnMarkers with
        | nil => exact (hreturnMarkers_ne hret).elim
        | cons marker remaining =>
            simp only [List.cons_append, List.map_cons]
            rw [controlMachine_run_one]
            cases bit <;> cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  have hreturn := run_mapLeft_markers
    (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
    lookupReturnIndexMarker cleanupReturnRewrite returnMarkers indexEnd
    (List.replicate visited.length indexSpent ++ processed :: baseLeft)
    (defaultSuffixSymbols suffix)
    (step_cleanupReturn_lookupMarker formulaValue clauseValue
      (applyPolarity positive false))
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig
          (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
          returnMarkers indexEnd
          (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          (defaultSuffixSymbols suffix)) =
      configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
        blank (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++
          defaultSuffixSymbols suffix)) := by
    simpa only [List.cons_append] using hreturn
  have hindexEnd :
      satControl.run 1
        (configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
          blank (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++
            defaultSuffixSymbols suffix))) =
      keepLeftScanConfig
        (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
        (List.replicate visited.length indexSpent) processed baseLeft
        (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
          defaultSuffixSymbols suffix) := by
    exact step_cleanupReturn_indexEnd_keepLeft
      formulaValue clauseValue (applyPolarity positive false)
      (List.replicate visited.length indexSpent) processed baseLeft
      ((returnMarkers.map cleanupReturnRewrite).reverse ++ defaultSuffixSymbols suffix)
  have hspent := run_mapLeft_markers
    (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
    (fun marker => marker = indexSpent)
    (fun _ => processed)
    (List.replicate visited.length indexSpent) processed baseLeft
    (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
      defaultSuffixSymbols suffix)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_cleanupIndex_spent formulaValue clauseValue
        (applyPolarity positive false) leftHead leftTail right)
    (by simp)
  have hspent' :
      satControl.run visited.length
        (keepLeftScanConfig
          (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
          (List.replicate visited.length indexSpent) processed baseLeft
          (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
            defaultSuffixSymbols suffix)) =
      configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive false)) blank
        baseLeft
        (processed ::
          ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
            processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
              defaultSuffixSymbols suffix) := by
    simpa using hspent
  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
          blank baseLeft
          (processed ::
            ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
              processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
                defaultSuffixSymbols suffix)) =
      defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited 0 restLiteralPayload restPayload
        suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    simp only [List.cons_append]
    rw [step_cleanupIndex_processed]
    unfold defaultLiteralEvaluatedConfig returnMarkers
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
  rw [controlMachine_run_add, hdefault]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hindexEnd]
  rw [controlMachine_run_add, hspent']
  exact hclean


/-- Scratch marker left by an out-of-range indexed lookup. Both already-spent
and still-live unary index cells must be normalized to `processed`. -/
def defaultIndexScratchMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = indexSpent ∨ symbol = indexLive

@[simp] theorem step_cleanupIndex_defaultScratch
    (formulaValue clauseValue literalValue : Bool)
    (symbol : SATMachineSymbol)
    (h : defaultIndexScratchMarker symbol)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupIndex formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (symbol :: right)) =
    configAt (cleanupIndex formulaValue clauseValue literalValue) blank leftTail
      (leftHead :: processed :: right) := by
  rcases h with rfl | rfl <;>
    cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

/-- Assignment exhaustion while at least one live unary index marker remains.
The machine does not keep searching for a nonexistent certificate bit: it
immediately selects the default value `false`, then cleans every spent/live
index marker before returning to `clauseFind`. -/
theorem run_lookupLoop_default_succ
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals indexTail : Nat)
    (visited restLiteralPayload restPayload suffix : BitString) :
    satControl.run
      (4 * visited.length + 2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + indexTail + 10)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited (indexTail + 1)
        restLiteralPayload restPayload [] suffix) =
    defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals visited (indexTail + 1)
      restLiteralPayload restPayload suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  let indexMarkers : List SATMachineSymbol :=
    List.replicate visited.length indexSpent ++
      indexSpent :: List.replicate indexTail indexLive
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hselect :
      satControl.run 1
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited (indexTail + 1)
          restLiteralPayload restPayload [] suffix) =
      configAt (lookupSkipRight formulaValue clauseValue positive) blank
        (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ suffix.map ofBool)) := by
    rw [controlMachine_run_one]
    unfold lookupLoopConfig baseLeft rightMarkers certMarkers
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    simp [List.append_assoc]
  have hright := run_keepRight_markers
    (lookupSkipRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers
    (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
    (separator :: certMarkers ++ suffix.map ofBool)
    (step_lookupSkipRight_marker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupSkipRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ (indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft))
          (separator :: certMarkers ++ suffix.map ofBool)) =
      configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ (indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft))
        (certMarkers ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    exact step_lookupSkipRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupSkipCertificate formulaValue clauseValue positive)
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ (indexSpent ::
      List.replicate indexTail indexLive ++ processed :: baseLeft))
    (suffix.map ofBool)
    (step_lookupSkipCertificate_marker formulaValue clauseValue positive)
    (lookupSkipCertificateMarkers_all variableCount visited)
  have hleftLayout :
      certMarkers.reverse ++
        (separator :: rightMarkers.reverse ++ (indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft)) =
      returnMarkers ++ indexEnd :: (indexMarkers ++ processed :: baseLeft) := by
    unfold certMarkers rightMarkers returnMarkers indexMarkers
    unfold lookupSkipCertificateMarkers lookupSkipRightMarkers
    unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers zeroLookupRightMarkers
    simp [List.reverse_append, List.append_assoc]
  have hdefault :
      satControl.run 1
        (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++
            (separator :: rightMarkers.reverse ++ (indexSpent ::
              List.replicate indexTail indexLive ++ processed :: baseLeft)))
          (suffix.map ofBool)) =
      keepLeftScanConfig
        (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
        returnMarkers indexEnd (indexMarkers ++ processed :: baseLeft)
        (defaultSuffixSymbols suffix) := by
    rw [hleftLayout]
    cases suffix with
    | nil =>
        unfold defaultSuffixSymbols
        cases hret : returnMarkers with
        | nil => exact (hreturnMarkers_ne hret).elim
        | cons marker remaining =>
            simp only [List.cons_append]
            rw [controlMachine_run_one]
            cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
    | cons bit rest =>
        unfold defaultSuffixSymbols
        cases hret : returnMarkers with
        | nil => exact (hreturnMarkers_ne hret).elim
        | cons marker remaining =>
            simp only [List.cons_append, List.map_cons]
            rw [controlMachine_run_one]
            cases bit <;> cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  have hreturn := run_mapLeft_markers
    (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
    lookupReturnIndexMarker cleanupReturnRewrite returnMarkers indexEnd
    (indexMarkers ++ processed :: baseLeft) (defaultSuffixSymbols suffix)
    (step_cleanupReturn_lookupMarker formulaValue clauseValue
      (applyPolarity positive false))
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig
          (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
          returnMarkers indexEnd (indexMarkers ++ processed :: baseLeft)
          (defaultSuffixSymbols suffix)) =
      configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
        blank (indexMarkers ++ processed :: baseLeft)
        (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++
          defaultSuffixSymbols suffix)) := by
    simpa only [List.cons_append] using hreturn
  have hindexEnd :
      satControl.run 1
        (configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive false))
          blank (indexMarkers ++ processed :: baseLeft)
          (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++
            defaultSuffixSymbols suffix))) =
      keepLeftScanConfig
        (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
        indexMarkers processed baseLeft
        (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
          defaultSuffixSymbols suffix) := by
    exact step_cleanupReturn_indexEnd_keepLeft
      formulaValue clauseValue (applyPolarity positive false)
      indexMarkers processed baseLeft
      ((returnMarkers.map cleanupReturnRewrite).reverse ++ defaultSuffixSymbols suffix)
  have hmarkers : ∀ marker ∈ indexMarkers, defaultIndexScratchMarker marker := by
    intro marker hm
    unfold indexMarkers at hm
    rw [List.mem_append] at hm
    rcases hm with hspent | htail
    · exact Or.inl (List.eq_of_mem_replicate hspent)
    · simp only [List.mem_cons] at htail
      rcases htail with rfl | hlive
      · exact Or.inl rfl
      · exact Or.inr (List.eq_of_mem_replicate hlive)
  have hscratch := run_mapLeft_markers
    (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
    defaultIndexScratchMarker (fun _ => processed)
    indexMarkers processed baseLeft
    (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
      defaultSuffixSymbols suffix)
    (step_cleanupIndex_defaultScratch formulaValue clauseValue
      (applyPolarity positive false)) hmarkers
  have hscratch' :
      satControl.run indexMarkers.length
        (keepLeftScanConfig
          (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
          indexMarkers processed baseLeft
          (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
            defaultSuffixSymbols suffix)) =
      configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive false)) blank
        baseLeft
        (processed :: (indexMarkers.map (fun _ => processed)).reverse ++
          processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
            defaultSuffixSymbols suffix) := by
    simpa using hscratch
  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
          blank baseLeft
          (processed :: (indexMarkers.map (fun _ => processed)).reverse ++
            processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++
              defaultSuffixSymbols suffix)) =
      defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited (indexTail + 1)
        restLiteralPayload restPayload suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    simp only [List.cons_append]
    rw [step_cleanupIndex_processed]
    unfold defaultLiteralEvaluatedConfig returnMarkers indexMarkers
    simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
      zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
    rw [show visited.length + (indexTail + 1) =
      (visited.length + indexTail) + 1 by omega]
    rw [List.replicate_succ]
    simp only [List.cons_append]
  have hlenRight : rightMarkers.length =
      visited.length + 1 + restLiteralPayload.length + restPayload.length := by
    exact lookupSkipRightMarkers_length _ _ _
  have hlenCert : certMarkers.length = variableCount + 1 + visited.length := by
    exact lookupSkipCertificateMarkers_length _ _
  have hlenReturn : returnMarkers.length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact lookupReturnIndexMarkers_length _ _ _ _
  have hlenIndex : indexMarkers.length = visited.length + indexTail + 1 := by
    unfold indexMarkers
    simp
    omega
  rw [show 4 * visited.length + 2 * variableCount +
      2 * (restLiteralPayload.length + restPayload.length) + indexTail + 10 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + (indexMarkers.length + 1))))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hdefault]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hindexEnd]
  rw [controlMachine_run_add, hscratch']
  exact hclean

/-- Uniform assignment-exhaustion theorem for any number of still-live unary
index markers. `extraIndex = 0` is the exact-boundary case; positive values are
strictly out of range. -/
def literalDefaultLookupCost
    (visitedCount variableCount restLiteralLength restPayloadLength extraIndex : Nat) : Nat :=
  4 * visitedCount + 2 * variableCount +
    2 * (restLiteralLength + restPayloadLength) + extraIndex + 9

theorem run_lookupLoop_default
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals extraIndex : Nat)
    (visited restLiteralPayload restPayload suffix : BitString) :
    satControl.run
      (literalDefaultLookupCost visited.length variableCount
        restLiteralPayload.length restPayload.length extraIndex)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited extraIndex
        restLiteralPayload restPayload [] suffix) =
    defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals visited extraIndex
      restLiteralPayload restPayload suffix := by
  cases extraIndex with
  | zero =>
      simpa [literalDefaultLookupCost] using
        run_lookupLoop_default_zero formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited restLiteralPayload restPayload suffix
  | succ indexTail =>
      unfold literalDefaultLookupCost
      have h := run_lookupLoop_default_succ formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals indexTail visited restLiteralPayload
        restPayload suffix
      rw [show 4 * visited.length + 2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + (indexTail + 1) + 9 =
        4 * visited.length + 2 * variableCount +
          2 * (restLiteralPayload.length + restPayload.length) + indexTail + 10 by omega]
      exact h


/-- Repeated indexed skipping with a residual unary-index tail. This is the
out-of-range analogue of `run_lookupLoop_prefix`: after consuming the concrete
assignment prefix, `extraIndex` live index markers remain. -/
theorem run_lookupLoop_prefix_extra
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals extraIndex : Nat)
    (visited skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (lookupSkipCostFrom visited.length variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited (skipped.length + extraIndex)
        restLiteralPayload restPayload (skipped ++ assignmentTail) suffix) =
    lookupLoopConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals (visited ++ skipped) extraIndex
      restLiteralPayload restPayload assignmentTail suffix := by
  induction skipped generalizing visited with
  | nil =>
      simp [lookupSkipCostFrom, lookupLoopConfig]
  | cons value rest ih =>
      change satControl.run
        (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
            restPayload.length +
          lookupSkipCostFrom (visited.length + 1) variableCount
            restLiteralPayload.length restPayload.length rest.length)
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited
          (rest.length + 1 + extraIndex)
          restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) = _
      rw [controlMachine_run_add]
      have hone := run_lookupLoop_one
        formulaValue clauseValue positive value variableCount remainingClauses
        remainingLiterals (rest.length + extraIndex) visited restLiteralPayload
        restPayload (rest ++ assignmentTail) suffix
      have hone' :
          satControl.run
            (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
              restPayload.length)
            (lookupLoopConfig formulaValue clauseValue positive variableCount
              remainingClauses remainingLiterals visited
              (rest.length + 1 + extraIndex)
              restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) =
          lookupLoopConfig formulaValue clauseValue positive variableCount
            remainingClauses remainingLiterals (visited ++ [value])
            (rest.length + extraIndex) restLiteralPayload restPayload
            (rest ++ assignmentTail) suffix := by
        rw [show rest.length + 1 + extraIndex = rest.length + extraIndex + 1 by omega]
        simpa [lookupSkipOneCost] using hone
      rw [hone']
      have hrest := ih (visited := visited ++ [value])
      simpa [List.append_assoc] using hrest

/-- Total lookup cost when the requested variable index is
`assignment.length + extraIndex`. -/
def literalLookupDefaultTotalCost
    (assignmentLength variableCount restLiteralLength restPayloadLength extraIndex : Nat) : Nat :=
  lookupSkipCostFrom 0 variableCount restLiteralLength restPayloadLength assignmentLength +
    literalDefaultLookupCost assignmentLength variableCount
      restLiteralLength restPayloadLength extraIndex

/-- Full assignment-exhaustion lookup from the literal lookup selector. The
requested index is exactly `assignment.length + extraIndex`, so `extraIndex = 0`
is the first missing variable and larger values are farther out of range. -/
theorem run_literalLookup_default_extra
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals extraIndex : Nat)
    (assignment restLiteralPayload restPayload suffix : BitString) :
    satControl.run
      (literalLookupDefaultTotalCost assignment.length variableCount
        restLiteralPayload.length restPayload.length extraIndex)
      (literalLookupSelectConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals (assignment.length + extraIndex)
        restLiteralPayload restPayload assignment suffix) =
    defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals assignment extraIndex
      restLiteralPayload restPayload suffix := by
  have hstart := literalLookupSelectConfig_eq_lookupLoopConfig
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals (assignment.length + extraIndex) restLiteralPayload
    restPayload assignment suffix
  have hskip := run_lookupLoop_prefix_extra
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals extraIndex ([] : BitString) assignment restLiteralPayload
    restPayload ([] : BitString) suffix
  have hskip' :
      satControl.run
        (lookupSkipCostFrom 0 variableCount restLiteralPayload.length
          restPayload.length assignment.length)
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals [] (assignment.length + extraIndex)
          restLiteralPayload restPayload assignment suffix) =
      lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals assignment extraIndex
        restLiteralPayload restPayload [] suffix := by
    simpa using hskip
  have hdefault := run_lookupLoop_default
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals extraIndex assignment restLiteralPayload restPayload suffix
  unfold literalLookupDefaultTotalCost
  rw [controlMachine_run_add]
  rw [hstart]
  rw [hskip']
  exact hdefault

/-- End-to-end cost from the canonical literal sign bit through unary index
parsing and an assignment-exhaustion lookup. -/
def literalDefaultEvaluationCost
    (assignmentLength variableCount restLiteralLength restPayloadLength extraIndex : Nat) : Nat :=
  assignmentLength + extraIndex + 2 +
    literalLookupDefaultTotalCost assignmentLength variableCount
      restLiteralLength restPayloadLength extraIndex

/-- End-to-end execution of a canonically encoded out-of-range literal. -/
theorem run_literal_default_extra
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals extraIndex : Nat)
    (assignment restLiteralPayload restPayload suffix : BitString) :
    satControl.run
      (literalDefaultEvaluationCost assignment.length variableCount
        restLiteralPayload.length restPayload.length extraIndex)
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate (assignment.length + extraIndex) true ++ [false])
        restLiteralPayload restPayload assignment suffix) =
    defaultLiteralEvaluatedConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals assignment extraIndex
      restLiteralPayload restPayload suffix := by
  have hparse := run_literal_to_lookupSelect
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals (assignment.length + extraIndex) restLiteralPayload
    restPayload assignment suffix
  have hlookup := run_literalLookup_default_extra
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals extraIndex assignment restLiteralPayload restPayload suffix
  unfold literalDefaultEvaluationCost
  rw [controlMachine_run_add, hparse]
  exact hlookup


/-- Boolean polarity tag used by the SAT machine's literal parser. -/
def cnfLiteralPositive : CNF.Literal → Bool
  | .positive _ => true
  | .negative _ => false

/-- Variable index carried by a CNF literal. -/
def cnfLiteralIndex : CNF.Literal → Nat
  | .positive index => index
  | .negative index => index

@[simp] theorem cnfLiteral_eval_eq_applyPolarity
    (assignment : CNF.Assignment) (literal : CNF.Literal) :
    CNF.Literal.eval assignment literal =
      applyPolarity (cnfLiteralPositive literal)
        (CNF.valueAt assignment (cnfLiteralIndex literal)) := by
  cases literal <;> rfl

@[simp] theorem cnf_valueAt_length_add
    (assignment : CNF.Assignment) (extraIndex : Nat) :
    CNF.valueAt assignment (assignment.length + extraIndex) = false := by
  simp [CNF.valueAt]

/-- CNF-semantic result of an out-of-range literal evaluation. The right tape
uses `defaultSuffixSymbols`, retaining the exact explicit-blank behavior of the
machine zipper when the physical suffix is empty. -/
def defaultCNFLiteralEvaluatedConfig
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal)) blank
    (clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate (assignment.length + extraIndex + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++
            defaultSuffixSymbols suffix)

/-- The machine-level default-value output is definitionally the CNF literal
semantics whenever the literal index is `assignment.length + extraIndex`. -/
theorem defaultLiteralEvaluatedConfig_eq_cnf
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString)
    (hindex : cnfLiteralIndex literal = assignment.length + extraIndex) :
    defaultLiteralEvaluatedConfig formulaValue clauseValue
      (cnfLiteralPositive literal) variableCount remainingClauses remainingLiterals
      assignment extraIndex restLiteralPayload restPayload suffix =
    defaultCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
      remainingClauses remainingLiterals assignment literal extraIndex
      restLiteralPayload restPayload suffix := by
  cases literal with
  | positive index =>
      simp only [cnfLiteralIndex, cnfLiteralPositive] at hindex ⊢
      subst index
      simp [defaultLiteralEvaluatedConfig, defaultCNFLiteralEvaluatedConfig,
        CNF.Literal.eval, CNF.valueAt, applyPolarity]
  | negative index =>
      simp only [cnfLiteralIndex, cnfLiteralPositive] at hindex ⊢
      subst index
      simp [defaultLiteralEvaluatedConfig, defaultCNFLiteralEvaluatedConfig,
        CNF.Literal.eval, CNF.valueAt, applyPolarity]

/-- Real-CNF out-of-range literal semantics. No assignment split is supplied by
hand: the only hypothesis is the exact arithmetic position of the literal
index beyond the assignment. -/
theorem run_cnfLiteral_default_extra
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals extraIndex : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString)
    (hindex : cnfLiteralIndex literal = assignment.length + extraIndex) :
    satControl.run
      (literalDefaultEvaluationCost assignment.length variableCount
        restLiteralPayload.length restPayload.length extraIndex)
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals (CNF.literalCodec.encode literal)
        restLiteralPayload restPayload assignment suffix) =
    defaultCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
      remainingClauses remainingLiterals assignment literal extraIndex
      restLiteralPayload restPayload suffix := by
  cases literal with
  | positive index =>
      simp only [cnfLiteralIndex] at hindex
      subst index
      rw [CNF.literalCodec_encode_positive_layout]
      have hrun := run_literal_default_extra formulaValue clauseValue true
        variableCount remainingClauses remainingLiterals extraIndex assignment
        restLiteralPayload restPayload suffix
      rw [hrun]
      exact defaultLiteralEvaluatedConfig_eq_cnf formulaValue clauseValue
        variableCount remainingClauses remainingLiterals assignment
        (.positive (assignment.length + extraIndex)) extraIndex
        restLiteralPayload restPayload suffix rfl
  | negative index =>
      simp only [cnfLiteralIndex] at hindex
      subst index
      rw [CNF.literalCodec_encode_negative_layout]
      have hrun := run_literal_default_extra formulaValue clauseValue false
        variableCount remainingClauses remainingLiterals extraIndex assignment
        restLiteralPayload restPayload suffix
      rw [hrun]
      exact defaultLiteralEvaluatedConfig_eq_cnf formulaValue clauseValue
        variableCount remainingClauses remainingLiterals assignment
        (.negative (assignment.length + extraIndex)) extraIndex
        restLiteralPayload restPayload suffix rfl


/-- Elementary list split used to eliminate hand-supplied assignment prefixes
from the in-range literal theorem. -/
theorem exists_assignment_split_of_lt
    (assignment : CNF.Assignment) (index : Nat)
    (h : index < assignment.length) :
    ∃ skipped value tail,
      assignment = skipped ++ value :: tail ∧ skipped.length = index := by
  induction assignment generalizing index with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases index with
      | zero =>
          exact ⟨[], head, tail, rfl, rfl⟩
      | succ index =>
          have htail : index < tail.length := by
            simpa using h
          obtain ⟨skipped, value, rest, hsplit, hlen⟩ := ih index htail
          refine ⟨head :: skipped, value, rest, ?_, ?_⟩
          · simp [hsplit]
          · simp [hlen]

/-- Exact cost chosen by the real literal index. In-range indices use the
ordinary target-read proof; exhausted indices use the default-false proof. -/
def cnfLiteralTotalEvaluationCost
    (assignmentLength variableCount restLiteralLength restPayloadLength index : Nat) : Nat :=
  if index < assignmentLength then
    literalEvaluationCost variableCount restLiteralLength restPayloadLength index
  else
    literalDefaultEvaluationCost assignmentLength variableCount
      restLiteralLength restPayloadLength (index - assignmentLength)

/-- Complete state-level semantics for every real CNF literal, with no
in-bounds hypothesis. The physical tape differs in the exhausted/empty-suffix
case by one explicit trailing blank, so this theorem intentionally states the
shared semantic state reached by both exact execution branches. -/
theorem run_cnfLiteral_total_state
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment) (literal : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    (satControl.run
      (cnfLiteralTotalEvaluationCost assignment.length variableCount
        restLiteralPayload.length restPayload.length (cnfLiteralIndex literal))
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals (CNF.literalCodec.encode literal)
        restLiteralPayload restPayload assignment suffix)).state =
    clauseFind formulaValue (clauseValue || CNF.Literal.eval assignment literal) := by
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
        simp [literalEvaluatedConfig, CNF.Literal.eval, CNF.valueAt,
          applyPolarity]
      · have hge : assignment.length ≤ index := by omega
        let extraIndex := index - assignment.length
        have hindex : index = assignment.length + extraIndex := by
          unfold extraIndex
          omega
        rw [CNF.literalCodec_encode_positive_layout]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        simp only [if_neg hlt]
        change
          (satControl.run
            (literalDefaultEvaluationCost assignment.length variableCount
              restLiteralPayload.length restPayload.length extraIndex)
            (firstLiteralSignConfig formulaValue clauseValue variableCount
              remainingClauses remainingLiterals
              (true :: List.replicate index true ++ [false])
              restLiteralPayload restPayload assignment suffix)).state = _
        rw [hindex]
        have hrun := run_cnfLiteral_default_extra formulaValue clauseValue
          variableCount remainingClauses remainingLiterals extraIndex assignment
          (.positive (assignment.length + extraIndex)) restLiteralPayload
          restPayload suffix rfl
        rw [CNF.literalCodec_encode_positive_layout] at hrun
        rw [hrun]
        rfl
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
        simp [literalEvaluatedConfig, CNF.Literal.eval, CNF.valueAt,
          applyPolarity]
      · have hge : assignment.length ≤ index := by omega
        let extraIndex := index - assignment.length
        have hindex : index = assignment.length + extraIndex := by
          unfold extraIndex
          omega
        rw [CNF.literalCodec_encode_negative_layout]
        unfold cnfLiteralTotalEvaluationCost cnfLiteralIndex
        simp only [if_neg hlt]
        change
          (satControl.run
            (literalDefaultEvaluationCost assignment.length variableCount
              restLiteralPayload.length restPayload.length extraIndex)
            (firstLiteralSignConfig formulaValue clauseValue variableCount
              remainingClauses remainingLiterals
              (false :: List.replicate index true ++ [false])
              restLiteralPayload restPayload assignment suffix)).state = _
        rw [hindex]
        have hrun := run_cnfLiteral_default_extra formulaValue clauseValue
          variableCount remainingClauses remainingLiterals extraIndex assignment
          (.negative (assignment.length + extraIndex)) restLiteralPayload
          restPayload suffix rfl
        rw [CNF.literalCodec_encode_negative_layout] at hrun
        rw [hrun]
        rfl

end SATMachineCertificatePhase
end OpenProblems.Complexity
