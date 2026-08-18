import OpenProblems.Complexity.SATMachineClauseHistoryPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- The canonical post-state of the first evaluated literal is exactly the
history-aware `clauseFind` state for the next literal.  The consumed literal
contributes one spent clause marker and `cnfLiteralIndex literal + 2`
processed tape cells (sign plus unary index including its terminator). -/
theorem canonicalCNFLiteralEvaluatedConfig_eq_clauseHistoryFindConfig_next
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment)
    (literal nextLiteral : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
      remainingClauses (remainingLiterals + 1) assignment literal
      (CNF.literalCodec.encode nextLiteral ++ restLiteralPayload)
      restPayload suffix =
    clauseHistoryFindConfig formulaValue
      (clauseValue || CNF.Literal.eval assignment literal)
      variableCount remainingClauses 1 remainingLiterals
      (cnfLiteralIndex literal + 2)
      (CNF.literalCodec.encode nextLiteral) restLiteralPayload restPayload
      assignment suffix := by
  unfold canonicalCNFLiteralEvaluatedConfig clauseHistoryFindConfig
  simp [List.map_append, List.append_assoc]

/-- Once one literal has been evaluated, selecting the next literal from the
canonical post-state has an exact normalized cost of
`cnfLiteralIndex literal + 8` transitions. -/
theorem run_canonicalCNFLiteralEvaluated_to_nextLiteralSign
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment)
    (literal nextLiteral : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    satControl.run (cnfLiteralIndex literal + 8)
      (canonicalCNFLiteralEvaluatedConfig formulaValue clauseValue variableCount
        remainingClauses (remainingLiterals + 1) assignment literal
        (CNF.literalCodec.encode nextLiteral ++ restLiteralPayload)
        restPayload suffix) =
    clauseHistoryLiteralSignConfig formulaValue
      (clauseValue || CNF.Literal.eval assignment literal)
      variableCount remainingClauses 1 remainingLiterals
      (cnfLiteralIndex literal + 2)
      (CNF.literalCodec.encode nextLiteral) restLiteralPayload restPayload
      assignment suffix := by
  rw [canonicalCNFLiteralEvaluatedConfig_eq_clauseHistoryFindConfig_next]
  have h := run_clauseHistoryFind_to_literalSign
    formulaValue (clauseValue || CNF.Literal.eval assignment literal)
    (CNF.literalSign nextLiteral)
    variableCount remainingClauses 1 remainingLiterals
    (cnfLiteralIndex literal + 2)
    (CNF.literalIndexBits nextLiteral)
    restLiteralPayload restPayload assignment suffix
  simpa [CNF.literalCodec_encode_layout] using h

/-- The actual total evaluator may differ from its canonical logical post-state
only by the already-proved trailing-blank relation.  Continuing through the
next-literal selector preserves that relation and lands, on the canonical side,
at the exact history-aware sign cursor. -/
theorem run_cnfLiteral_total_then_nextSelector_trailingBlankRel
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (assignment : CNF.Assignment)
    (literal nextLiteral : CNF.Literal)
    (restLiteralPayload restPayload suffix : BitString) :
    trailingBlankRel blank
      (clauseHistoryLiteralSignConfig formulaValue
        (clauseValue || CNF.Literal.eval assignment literal)
        variableCount remainingClauses 1 remainingLiterals
        (cnfLiteralIndex literal + 2)
        (CNF.literalCodec.encode nextLiteral) restLiteralPayload restPayload
        assignment suffix)
      (satControl.run (cnfLiteralIndex literal + 8)
        (satControl.run
          (cnfLiteralTotalEvaluationCost assignment.length variableCount
            ((CNF.literalCodec.encode nextLiteral ++ restLiteralPayload).length)
            restPayload.length (cnfLiteralIndex literal))
          (firstLiteralSignConfig formulaValue clauseValue variableCount
            remainingClauses (remainingLiterals + 1)
            (CNF.literalCodec.encode literal)
            (CNF.literalCodec.encode nextLiteral ++ restLiteralPayload)
            restPayload assignment suffix))) := by
  have hrel := run_cnfLiteral_total_trailingBlankRel
    formulaValue clauseValue variableCount remainingClauses
    (remainingLiterals + 1) assignment literal
    (CNF.literalCodec.encode nextLiteral ++ restLiteralPayload)
    restPayload suffix
  have hrun := trailingBlankRel_run satControl (cnfLiteralIndex literal + 8)
    _ _ hrel
  rw [run_canonicalCNFLiteralEvaluated_to_nextLiteralSign] at hrun
  exact hrun

end SATMachineCertificatePhase
end OpenProblems.Complexity
