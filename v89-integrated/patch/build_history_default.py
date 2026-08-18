from pathlib import Path
import re, sys
root=Path(sys.argv[1])
out=root/'OpenProblems/Complexity/SATMachineClauseLiteralHistoryDefaultPhase.lean'
s=(root/'OpenProblems/Complexity/SATMachineDefaultLookupPhase.lean').read_text()

def extract(start,end,after=0):
    i=s.index(start,after); j=s.index(end,i); return s[i:j]

raw={}
raw['zero']=extract('theorem run_lookupLoop_default_zero','/-- Scratch marker left')
raw['succ']=extract('theorem run_lookupLoop_default_succ','/-- Uniform assignment-exhaustion theorem')
pos=s.index('def literalDefaultLookupCost')
raw['default']=extract('theorem run_lookupLoop_default\n','/-- Repeated indexed skipping',pos)
raw['prefix']=extract('theorem run_lookupLoop_prefix_extra','/-- Total lookup cost')
raw['lookup']=extract('theorem run_literalLookup_default_extra','/-- End-to-end cost')
raw['literal']=extract('theorem run_literal_default_extra','/-- Boolean polarity tag')

name_map={
'run_lookupLoop_default_zero':'run_historyLookupLoop_default_zero',
'run_lookupLoop_default_succ':'run_historyLookupLoop_default_succ',
'run_lookupLoop_default':'run_historyLookupLoop_default',
'run_lookupLoop_prefix_extra':'run_historyLookupLoop_prefix_extra',
'run_literalLookup_default_extra':'run_historyLiteralLookup_default_extra',
'run_literal_default_extra':'run_historyLiteral_default_extra',
'run_lookupLoop_one':'run_historyLookupLoop_one',
'run_literal_to_lookupSelect':'run_historyLiteral_to_lookupSelect',
}
func_map={
'lookupLoopConfig':'historyLookupLoopConfig',
'literalLookupSelectConfig':'historyLiteralLookupSelectConfig',
'firstLiteralSignConfig':'historyFirstLiteralSignConfig',
'defaultLiteralEvaluatedConfig':'historyDefaultLiteralEvaluatedRawConfig',
'literalLookupSelectConfig_eq_lookupLoopConfig':'historyLiteralLookupSelectConfig_eq_historyLookupLoopConfig',
}

def transform(block):
    orig=re.search(r'theorem\s+(\w+)',block).group(1)
    new=block.replace('theorem '+orig,'theorem '+name_map[orig]+'\n    (processedLiterals processedWidth : Nat)',1)
    for old in sorted(name_map,key=len,reverse=True):
        new=new.replace(old,name_map[old]+' processedLiterals processedWidth')
    bad=name_map[orig]+' processedLiterals processedWidth\n    (processedLiterals'
    new=new.replace(bad,name_map[orig]+'\n    (processedLiterals',1)
    for old in sorted(func_map,key=len,reverse=True):
        new=new.replace(old,func_map[old]+' processedLiterals processedWidth')
    for nm in func_map.values():
        new=new.replace('unfold '+nm+' processedLiterals processedWidth','unfold '+nm)
        new=new.replace(nm+' processedLiterals processedWidth] ',nm+'] ')
        new=new.replace(nm+' processedLiterals processedWidth,',nm+',')
    return new
tr={k:transform(v) for k,v in raw.items()}

old_base='''  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]'''
new_base='''  let baseLeft : List SATMachineSymbol :=
    List.replicate processedWidth processed ++ clauseEnd ::
      List.replicate (processedLiterals + 1) clauseSpent ++
        List.replicate remainingLiterals clauseLive ++
          formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
            variableEnd :: List.replicate variableCount variableChecked ++ [blank]'''
for k in ('zero','succ'):
    if old_base not in tr[k]: print('base missing',k)
    tr[k]=tr[k].replace(old_base,new_base,1)

header='''import OpenProblems.Complexity.SATMachineClauseLiteralHistoryValidPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- Raw out-of-range result in an arbitrary clause-history context. -/
def historyDefaultLiteralEvaluatedRawConfig
    (processedLiterals processedWidth : Nat)
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (extraIndex : Nat)
    (restLiteralPayload restPayload suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let clauseTail :=
    List.replicate (processedLiterals + 1) clauseSpent ++
      List.replicate remainingLiterals clauseLive ++
        formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
          variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload :=
    List.replicate (visited.length + extraIndex + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentSymbol ++
            defaultSuffixSymbols suffix
  match processedWidth with
  | 0 =>
      configAt
        (clauseFind formulaValue (clauseValue || applyPolarity positive false)) blank
        clauseTail (clauseEnd :: payload)
  | p + 1 =>
      configAt
        (clauseFind formulaValue (clauseValue || applyPolarity positive false)) blank
        (List.replicate p processed ++ clauseEnd :: clauseTail)
        (processed :: payload)

'''

for k,extra in [('zero','0'),('succ','(indexTail + 1)')]:
    b=tr[k]
    i=b.index('  have hclean :')
    j=b.index('  have hlenRight',i)
    hclean=f'''  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive false))
          blank baseLeft
          (processed :: {'((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++\n              processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++\n                defaultSuffixSymbols suffix)' if k=='zero' else '(indexMarkers.map (fun _ => processed)).reverse ++\n            processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++\n              defaultSuffixSymbols suffix)'}) =
      historyDefaultLiteralEvaluatedRawConfig processedLiterals processedWidth formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited {extra}
        restLiteralPayload restPayload suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    cases processedWidth with
    | zero =>
        simp only [List.replicate_zero, List.nil_append, List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold historyDefaultLiteralEvaluatedRawConfig returnMarkers{' indexMarkers' if k=='succ' else ''}
        simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
{'        rw [show visited.length + (indexTail + 1) =\n          (visited.length + indexTail) + 1 by omega]\n        rw [List.replicate_succ]\n        simp only [List.cons_append]\n' if k=='succ' else ''}    | succ p =>
        rw [List.replicate_succ]
        simp only [List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold historyDefaultLiteralEvaluatedRawConfig returnMarkers{' indexMarkers' if k=='succ' else ''}
        simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
{'        rw [show visited.length + (indexTail + 1) =\n          (visited.length + indexTail) + 1 by omega]\n        rw [List.replicate_succ]\n        simp only [List.cons_append]\n' if k=='succ' else ''}'''
    tr[k]=b[:i]+hclean+b[j:]

body=header+'\n'.join(tr[k] for k in ('zero','succ','default','prefix','lookup','literal'))
body=body.replace('historyLiteralLookupSelectConfig processedLiterals processedWidth_eq_historyLookupLoopConfig processedLiterals processedWidth','historyLiteralLookupSelectConfig_eq_historyLookupLoopConfig processedLiterals processedWidth')
body=body.replace('simp [lookupSkipCostFrom, historyLookupLoopConfig processedLiterals processedWidth]', 'simp [lookupSkipCostFrom, historyLookupLoopConfig]')
body+='\nend SATMachineCertificatePhase\nend OpenProblems.Complexity\n'
out.write_text(body)
print(out)
