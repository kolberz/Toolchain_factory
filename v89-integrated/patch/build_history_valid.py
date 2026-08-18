from pathlib import Path
import re
import sys

root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
out = root / "OpenProblems/Complexity/SATMachineClauseLiteralHistoryValidPhase.lean"
lp = (root / "OpenProblems/Complexity/SATMachineLookupPhase.lean").read_text()
lit = (root / "OpenProblems/Complexity/SATMachineLiteralPhase.lean").read_text()

def extract(text, start, end):
    s = text.index(start)
    e = text.index(end, s)
    return text[s:e]

raw = {
    "sign": extract(lit, "theorem run_literalSign_to_indexRead", "@[simp] theorem step_indexRead_true"),
    "indextolook": extract(lit, "theorem run_indexRead_to_lookupSelect", "/-- A canonically encoded literal reaches"),
    "tolook": extract(lit, "theorem run_literal_to_lookupSelect", "/-- Symbols crossed to the right"),
    "one": extract(lp, "theorem run_lookupLoop_one", "/-- Generic exact left scan"),
    "target": extract(lp, "theorem run_lookupLoop_target", "/-- Exact cost of one indexed"),
    "prefix": extract(lp, "theorem run_lookupLoop_prefix", "/-- Exact total cost of a valid"),
    "lookupvalid": extract(lp, "theorem run_literalLookup_valid", "/-- Exact end-to-end cost"),
    "literalvalid": extract(lp, "theorem run_literal_valid", "end SATMachineCertificatePhase"),
}

name_map = {
    "run_literalSign_to_indexRead": "run_historyLiteralSign_to_indexRead",
    "run_indexRead_to_lookupSelect": "run_historyIndexRead_to_lookupSelect",
    "run_literal_to_lookupSelect": "run_historyLiteral_to_lookupSelect",
    "run_lookupLoop_one": "run_historyLookupLoop_one",
    "run_lookupLoop_target": "run_historyLookupLoop_target",
    "run_lookupLoop_prefix": "run_historyLookupLoop_prefix",
    "run_literalLookup_valid": "run_historyLiteralLookup_valid",
    "run_literal_valid": "run_historyLiteral_valid",
}
func_map = {
    "firstLiteralSignConfig": "historyFirstLiteralSignConfig",
    "literalIndexEntryConfig": "historyLiteralIndexEntryConfig",
    "literalLookupSelectConfig": "historyLiteralLookupSelectConfig",
    "lookupLoopConfig": "historyLookupLoopConfig",
    "literalEvaluatedConfig": "historyLiteralEvaluatedRawConfig",
}

def transform(block):
    theorem_orig = re.search(r"theorem\s+(\w+)", block).group(1)
    new = block.replace(
        "theorem " + theorem_orig,
        "theorem " + name_map[theorem_orig] + "\n    (processedLiterals processedWidth : Nat)",
        1,
    )
    for old, new_name in name_map.items():
        new = new.replace(old, new_name + " processedLiterals processedWidth")
    bad = name_map[theorem_orig] + " processedLiterals processedWidth\n    (processedLiterals"
    new = new.replace(bad, name_map[theorem_orig] + "\n    (processedLiterals", 1)
    for old, new_name in func_map.items():
        new = new.replace(old, new_name + " processedLiterals processedWidth")
    for new_name in func_map.values():
        new = new.replace(
            "unfold " + new_name + " processedLiterals processedWidth",
            "unfold " + new_name,
        )
    return new

tr = {key: transform(block) for key, block in raw.items()}

old_base = '''  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]'''
new_base = '''  let baseLeft : List SATMachineSymbol :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]'''
for key in ("one", "target"):
    tr[key] = tr[key].replace(old_base, new_base)

header = '''import OpenProblems.Complexity.SATMachineClauseRecursionPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

def historyFirstLiteralSignConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (literalBits restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  clauseHistoryLiteralSignConfig formulaValue clauseValue variableCount
    remainingClauses processedLiterals remainingLiterals processedWidth
    literalBits restLiteralPayload restPayload assignment suffix

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

'''

body = header + "\n".join(
    tr[key] for key in
    ("sign", "indextolook", "tolook", "one", "target", "prefix", "lookupvalid", "literalvalid")
)

body = body.replace(
    "unfold historyFirstLiteralSignConfig historyLiteralIndexEntryConfig processedLiterals processedWidth\n",
    "unfold historyFirstLiteralSignConfig clauseHistoryLiteralSignConfig historyLiteralIndexEntryConfig\n",
    1,
)

old_parser_base = '''  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload : List SATMachineSymbol :='''
new_parser_base = new_base + "\n  let payload : List SATMachineSymbol :="
body = body.replace(old_parser_base, new_parser_base, 1)

body = body.replace(
    "historyLiteralLookupSelectConfig processedLiterals processedWidth_eq_historyLookupLoopConfig processedLiterals processedWidth",
    "historyLiteralLookupSelectConfig_eq_historyLookupLoopConfig processedLiterals processedWidth",
)

old_hclean = '''  have hclean :
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
    simp only [List.cons_append]
    rw [step_cleanupIndex_processed]
    unfold historyLiteralEvaluatedRawConfig assignmentRight returnMarkers
    simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
      zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
'''
new_hclean = '''  have hclean :
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
'''
if old_hclean not in body:
    raise SystemExit("target hclean pattern not found")
body = body.replace(old_hclean, new_hclean, 1)

body += "\nend SATMachineCertificatePhase\nend OpenProblems.Complexity\n"
out.write_text(body)
print(out)
