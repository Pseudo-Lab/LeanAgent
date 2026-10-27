"""Static integrity checks only. This command does not establish Lean validity."""
from pathlib import Path
import argparse,json,tempfile
import experiment

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--arena',type=Path,required=True)
p.add_argument('--candidates',type=Path,required=True)
a=p.parse_args()
rows,starting=experiment.inputs()
cs=json.loads(a.candidates.read_text())
assert cs['startingSnapshotSha256']==experiment.IDENTITY['startingSha256']
assert set(cs['problems'])=={str(i) for i in range(1,16)}
with tempfile.TemporaryDirectory() as tmp:
 _,tokens,_,p12=experiment.load_checkers(a.arena.resolve(),Path(tmp))
 checked=[]
 for problem,candidates in cs['problems'].items():
  pid=int(problem);meta=rows[pid-1];parent=starting['problems'][pid-1]
  parent_code=(experiment.HERE/'starting'/f'P{pid:02}.lean').read_bytes()
  assert experiment.sha(parent_code)==parent['candidateHash']
  seen=set()
  for c in candidates:
   assert experiment.sha(c['proof'].encode())==c['candidateHash']
   assert c['candidateHash']!=parent['candidateHash'] and c['candidateHash'] not in seen
   seen.add(c['candidateHash'])
   if pid==12:count=p12.gate(c['proof'],meta['statement'],tokens)
   else:
    tokens.validate_declaration(c['proof'],meta['statement'])
    count=tokens.proof_tokens(c['proof'],meta['statement'])
   checked.append({'problem':pid,'id':c['id'],'sha256':c['candidateHash'],'tokens':count})
 # Keep a negative control: a shortened declaration containing an admission must fail.
 for pid in (9,12):
  code=rows[pid-1]['statement']+' := by sorry\n'
  try:
   if pid==12:p12.gate(code,rows[pid-1]['statement'],tokens)
   else:tokens.validate_declaration(code,rows[pid-1]['statement'])
  except ValueError:pass
  else:raise AssertionError('Admission was accepted')
 print(json.dumps({'staticIntegrity':True,'candidateCount':len(checked),'checks':checked,
                   'leanCompilationPerformed':False},ensure_ascii=False,indent=2))
