"""Check the separate older-module audit detects an indirect sorry dependency."""
import re
from common import rows,read,write,run_dir,log
from tasks import make,backend
from prepare import inventory

def main():
    checks=[]
    for version in ('v4.27.0','v4.29.1'):
        dest=run_dir()/'controls/module_audit'/version
        if (dest/'result.json').exists():checks.append(read(dest/'result.json'));continue
        env=inventory()['strata-'+version];original=make(3,env);row=rows()[2]
        declared=re.search(r'\b(?:theorem|lemma)\s+([\w\'.]+)',row['statement'])[1]
        helper=row['statement'].replace(declared,'experiment_gap_helper',1)
        start=original.text.index(row['src'].rstrip())
        decorator=original.text[original.declaration_start:start]
        fixture=original.text[:original.declaration_start]+decorator+helper+' := by\n  sorry\n\n'+original.text[original.declaration_start:]
        t=make(3,env,'indirect_audit_control',text=fixture)
        trace,runner,v=backend(dest/'validation',t)
        prepared=v.prepare();write(trace.directory/'prepare.json',prepared.to_dict())
        result=v.verify('by\n  apply experiment_gap_helper <;> assumption','indirect_sorry') if prepared.status=='candidate_pass' else prepared
        value=dict(environment=env['id'],prepared=prepared.to_dict(),result=result.to_dict(),
            passed=result.status=='incomplete' and result.axioms is not None and 'sorryAx' in result.axioms,new_model_calls=0)
        write(dest/'result.json',value);checks.append(value);log('module_axiom_control',environment=env['id'],status=result.status,passed=value['passed'])
    write(run_dir()/'analysis/module_audit_controls.json',dict(checks=checks,passed=all(c['passed'] for c in checks)))

if __name__=='__main__':main()
