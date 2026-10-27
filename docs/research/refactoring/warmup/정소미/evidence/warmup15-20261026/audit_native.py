"""Independently reconstruct native P01-P06 sources from pinned Git and verify saved logs."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,statistics,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--arena',type=Path,required=True);p.add_argument('--runs',type=Path,required=True);p.add_argument('--benchmark',type=Path,required=True);p.add_argument('--runtime',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
sys.path.insert(0,str(a.runtime));from refactor_eval.lean import render,ALLOWED_AXIOMS
from refactor_eval.tokens import proof_tokens
spec=importlib.util.spec_from_file_location('pins',a.arena/'scripts/verify_warmup_pins.py');pins=importlib.util.module_from_spec(spec);spec.loader.exec_module(pins)
rows=[json.loads(l) for l in a.benchmark.read_text().splitlines()]
sha=lambda b:hashlib.sha256(b).hexdigest()
count=0;measurements=0;receipts=[]
for f in sorted(a.runs.glob('P*/**/result.json')):
 x=json.loads(f.read_text())
 if 'proofSha256' not in x:continue
 meta=rows[x['id']-1];code=(f.parent/'proof.lean').read_bytes().decode();assert sha(code.encode())==x['proofSha256']
 fp=x['fingerprint'];proj=Path(fp['project']);rev=fp['git']['head']
 source=subprocess.check_output(['git','-C',str(proj),'show',rev+':'+meta['file_path']]).decode()
 assert sha(source.encode())==x['sourceSha256']
 template,lead=pins.template(meta,source);assert sha(template.encode())==fp['template_sha256']
 assert x['result']['tokens']==proof_tokens(lead+code,lead+meta['statement'])
 for version,e in x['result']['environments'].items():
  assert any(pin.get(version)==rev for pin in meta['version_info'])
  values=[]
  for run in e['runs']:
   folder=f.parent/'evaluation'/version;src=(folder/run['source']).read_bytes();log=(folder/run['log']).read_bytes()
   assert sha(src)==run['source_sha256'] and sha(log)==run['log_sha256']
   match=re.search(r'(?m)^#refactor_eval "([^"]+)"',src.decode());nonce=match[1] if match else None
   assert src.decode()==render(template,lead+code,meta['name'],nonce), (str(f),run['source'],nonce)
   if 'measurement' in run:
    found=re.findall(r'REFACTOR_EVAL '+re.escape(nonce)+r' (\{[^\n]+\})',log.decode())
    assert len(found)==1;actual=json.loads(found[0]);assert actual==run['measurement']
    assert actual['target']==meta['name'] and actual['scaled']==actual['raw']//1000
    assert set(actual['axioms'])<=ALLOWED_AXIOMS and run['returncode']==0 and not run['timed_out']
    values.append(actual['scaled']);measurements+=1
   count+=1
  if e['valid']:
   assert len(values)==x['repetitions'] and statistics.median(values)==e['median_heartbeats']
  if x['result']['valid']:assert e['valid']
 receipts.append({'path':str(f.relative_to(a.runs)),'sha256':sha(f.read_bytes()),'valid':x['result']['valid']})
a.output.write_text(json.dumps({'auditedResults':len(receipts),'auditedLeanSourcesAndLogs':count,'auditedMeasurements':measurements,'mismatches':0,'receipts':receipts},indent=2)+'\n');print('Audited',len(receipts),count,measurements)
