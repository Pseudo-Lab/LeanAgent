"""Assemble the 15-proof selection from audited receipts, keeping prior controls explicit."""
from pathlib import Path
import argparse,json,hashlib,shutil
BASE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--runs-dir',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
R=args.runs_dir.resolve();D=args.output.resolve();D.mkdir(parents=True,exist_ok=False)
S=json.loads((BASE/'starting-selection.json').read_text())
def relative_receipt(path):
 p=Path(path)
 try:return str(p.relative_to(R))
 except ValueError:
  parts=p.parts
  for n,part in enumerate(parts):
   if part.startswith('ci-'):return str(Path(*parts[n:]))
  raise ValueError('Unrecognized archived receipt path: '+str(path))
A=json.loads((R/'p01-p06/summary.json').read_text())
B=json.loads((R/'p07-p09/summary.json').read_text())
C=json.loads((R/'p10-p15/summary.json').read_text())
G=json.loads((BASE/'candidates.json').read_text())
assert not C['summaryReadErrors']
assert not any(x['artifactErrors'] for x in C['attempts'])
sha=lambda x:hashlib.sha256(x).hexdigest()
score=lambda x,b:50*(2-x['tokens']/b['tokens']-x['heartbeats']/b['heartbeats'])
meta=lambda x:{'tokens':x['tokens'],'heartbeats':x['medianHeartbeats']}
rows=[];attempts=[]
for p in S['problems']:
 i=p['id']; original=p['baseline']; before=p['candidate'];after=before.copy();digest=p['candidateHash'];code=(BASE/'starting'/f'P{i:02}.lean').read_bytes()
 evidence=[];compat=[{'version':v['version'],'revision':v['revision'],'status':v['status'],'origin':'starting_snapshot'} for v in p['versions']]
 candidate_id=p['selectedCandidateId'];delta=0;new=False
 if i<=6:
  a=next(x for x in A['problems'] if x['id']==i)
  for t in a['attempts']:
   attempts.append({'problem':i,'id':t['id'],'sha256':t['sha256'],'valid':t['valid'],'status':t['status'],'tokens':t['tokens'],'heartbeats':t['heartbeats'],'evidence':'p01-p06/'+t['result'] if t['result'] else None})
  if a['status']=='improvement_confirmed':
   c=a['comparison'];assert c['repetitionsEach']==3
   assert c['startingEvidence']['proofSha256']==p['candidateHash']
   for name in ('originalEvidence','startingEvidence','candidateEvidence'):
    e=c[name];assert e['valid']
    assert all(v['valid'] and len(v['scaledRuns'])==3 for v in e['environments'].values())
    evidence.append('p01-p06/'+e['result'])
   original,before,after=c['original'],c['before'],c['after'];digest=a['selectedProofSha256'];code=(R/'p01-p06'/a['winnerProof']).read_bytes()
   candidate_id=c['chosenScreen'];new=True
   compat=[{'version':v['version'],'status':v['status'],'origin':'this_run','evidence':'p01-p06/'+v['result']} for v in a['versionResults']]
 elif i<=9:
  b=next(x for x in B['problems'] if x['problemId']==i)
  for t in B['attempts']:
   if t['problemId']==i: attempts.append({'problem':i,'id':t['candidate'],'sha256':t['candidateSha256'],'valid':t['valid'],'status':'passed' if t['valid'] else 'failed','tokens':t['tokens'],'heartbeats':t['medianHeartbeats'],'evidence':'p07-p09/'+t['evidence']})
  assert b['newImprovement']
  assert b['previousBest']['candidateSha256']==p['candidateHash']
  assert len({b[k]['templateSha256'] for k in ['original','previousBest','selected']})==1
  original,before,after=map(meta,[b['original'],b['previousBest'],b['selected']])
  digest=b['selected']['candidateSha256'];code=(R/'p07-p09'/b['selected']['proofPath']).read_bytes();candidate_id=b['selected']['candidate'];new=True
  for name in ['original','previousBest','selected']:
   assert b[name]['valid'] and len(b[name]['scaledHeartbeats'])==3
   evidence.append('p07-p09/'+b[name]['evidence'])
  compat=[]
  for c in b['compatibility']:
   assert c['selected']['valid'] and len(c['selected']['scaledHeartbeats'])==3
   if 'original' in c: assert c['original']['valid']
   assert c['selected']['candidateSha256']==digest
   compat.append({'version':c['version'],'status':'pass','origin':'this_run','evidence':'p07-p09/'+c['selected']['evidence'],'originalRemeasured':'original' in c,'note':c.get('note')})
 else:
  groups=[x for x in C['candidates'] if x['problem']==i and x['role']=='candidate']
  eligible=[];primary_candidates=[]
  for g in groups:
   rs=[x for x in C['attempts'] if x['problem']==i and x['sha256']==g['sha256'] and x['primary']]
   assert rs
   t=max(rs,key=lambda x:x['startedAt'])
   assert t['controlsValid'], 'Primary controls did not pass; do not count this as a proof failure'
   attempts.append({'problem':i,'id':t['id'],'sha256':t['sha256'],'valid':t['valid'],'status':'passed' if t['valid'] else 'failed','tokens':t['tokens'],'heartbeats':t['heartbeats'],'evidence':relative_receipt(t['rawSummary'])})
   primary_candidates.append((t,g))
   if g['compatibilityComplete'] and t['valid'] and t['controlsValid'] and t['scoreDeltaVersusStarting']>0:eligible.append((t,g))
  best_ready=max([t['scoreDeltaVersusStarting'] for t,g in eligible],default=0)
  for t,g in primary_candidates:
   if t['valid'] and t['controlsValid'] and t['scoreDeltaVersusStarting']>best_ready:
    assert not any(v['status']=='pending' for v in g['compatibility']), 'A stronger candidate still needs compatibility verification'
  if eligible:
   t,g=max(eligible,key=lambda z:z[0]['scoreDeltaVersusStarting'])
   controls=[x for x in C['attempts'] if x['problem']==i and x['rawSummary']==t['rawSummary']]
   orig=next(x for x in controls if x['role']=='original');prev=next(x for x in controls if x['role']=='starting')
   def rm(x):return {'tokens':x['tokens'],'heartbeats':x['heartbeats']}
   original,before,after=map(rm,[orig,prev,t]);digest=t['sha256'];candidate_id=t['id'];new=True
   proof=next(x['proof'] for x in G['problems'][str(i)] if x['candidateHash']==digest);code=proof.encode()
   evidence=[relative_receipt(t['rawSummary'])]
   compat=[{'version':v['version'],'status':v['status'],'origin':'this_run','evidence':[relative_receipt(s) for s in v['evidence']]} for v in g['compatibility']]
 assert sha(code)==digest
 assert set(v['version'] for v in compat)==set(v['version'] for v in p['versions']) and all(v['status']=='pass' for v in compat)
 if new:
  delta=score(after,original)-score(before,original);assert delta>0
 assert new or digest==p['candidateHash']
 (D/'selected').mkdir(exist_ok=True);(D/'selected'/f'P{i:02}.lean').write_bytes(code)
 rows.append({'problem':i,'name':p['name'],'countsInCommonScore':i!=12,'primaryVersion':p['environment'].split(' · ')[0],
  'status':'improved' if new else 'retained','original':original,'before':before,'after':after,'additionalPoints':delta,
  'selectedId':candidate_id,'selectedSha256':digest,'startingSha256':p['candidateHash'],'evidence':evidence,
  'compatibility':compat,'selectedProof':f'selected/P{i:02}.lean'})
# Every generated distinct proof must correspond to an actually executed attempt.
expected={(int(p),c['candidateHash']) for p,cs in G['problems'].items() for c in cs}
actual={(a['problem'],a['sha256']) for a in attempts}
assert expected==actual,('not executed',expected-actual,'not reproduced',actual-expected)
result={'schemaVersion':1,'startingSnapshotSha256':sha((BASE/'starting-selection.json').read_bytes()),
 'attempts':len(attempts),'validAttempts':sum(a['valid'] for a in attempts),'failedAttempts':sum(not a['valid'] for a in attempts),
 'improvedProblems':[r['problem'] for r in rows if r['status']=='improved'],
 'meanBeforeCommonPoints':sum(score(r['before'],r['original']) for r in rows if r['countsInCommonScore'])/14,
 'meanAfterCommonPoints':sum(score(r['after'],r['original']) for r in rows if r['countsInCommonScore'])/14,
 'meanAdditionalCommonPoints':sum(r['additionalPoints'] for r in rows if r['countsInCommonScore'])/14,
 'note':'New deltas use paired controls from each problem\u2019s primary environment. Retained rows preserve prior measurements and version evidence; they are not new improvements. P12 is separate.',
 'problems':rows}
(D/'selection.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
(D/'attempts.json').write_text(json.dumps(attempts,ensure_ascii=False,indent=2)+'\n')
shutil.copy2(BASE/'candidates.json',D/'candidates.json')
print(json.dumps({k:v for k,v in result.items() if k!='problems'},ensure_ascii=False,indent=2))
