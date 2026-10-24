"""V-A: identical candidates, three judges and independently frozen truth labels."""
import re
from common import read,write,sha,run_dir,log
from tasks import task,backend
from lean_repair.contracts import VerificationResult,StatementMismatch

VARIANTS=('correct','proof_error','incomplete','direct_sorry','changed_statement','indirect_sorry')

def indirect_body(p):
    return {4:'by\n  exact experiment_gap_helper μ hf hg',
        7:'by\n  exact experiment_gap_helper der',
        10:'by\n  exact experiment_gap_helper 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f h_fw_dist_lt',
        12:'by\n  exact experiment_gap_helper (MC := MC) hC_proximityGapAffineLines h_interleaved_gaps'}.get(p,'by\n  apply experiment_gap_helper <;> assumption')

def execute(p,variants=VARIANTS):
    t=task(p);cal=read(run_dir()/'calibration'/f'P{p}.json')
    trace,runner,v=backend(run_dir()/'V_A'/f'P{p}'/'ordinary',t,7200)
    v.environment=cal['environment'];v.environment_id=cal['environment_id']
    truth=read(run_dir()/'fixtures'/f'P{p}'/'expected.json')
    for kind in variants:
        dest=run_dir()/'V_A'/f'P{p}'/f'{kind}.json'
        if dest.exists():continue
        target,verifier=t,v
        if kind=='indirect_sorry':
            target=task(p,'indirect_fixture');_,_,verifier=backend(run_dir()/'V_A'/f'P{p}'/'indirect',target)
            prepared=verifier.prepare();write(verifier.out/'prepare.json',prepared.to_dict())
            if prepared.status!='candidate_pass':raise RuntimeError(f'P{p} indirect fixture context failed: {prepared.status}')
            body=indirect_body(p)
        elif kind=='correct':body=t.initial_body
        elif kind in ('proof_error','incomplete'):body=task(p,kind).initial_body
        elif kind=='direct_sorry':body='by\n  sorry'
        else:body='by\n  trivial'
        text=target.assemble(body)
        if kind=='changed_statement':
            name=re.search(r'\b(?:theorem|lemma)\s+([\w\'.]+)',target.text[target.declaration_start:target.body_start])[1]
            text=target.text[:target.declaration_start]+f'theorem {name} : True := {body}'+target.text[target.body_end:]
        candidate=run_dir()/'fixtures'/f'P{p}'/f'{kind}.lean';candidate.write_text(text)
        directory,proc,diagnostics,unparsed=verifier._run(text,kind+'_exitcode')
        failure=verifier._process_status(proc)
        a1='abstain' if failure else 'accept' if proc['returncode']==0 else 'reject'
        goals=selected=evidence=None
        if a1=='accept':
            verifier._context(text,diagnostics,kind+'_native_goals')
            folder=sorted((verifier.out/'lean').glob('*_'+kind+'_native_goals_context'))[-1]
            evidence=str(folder/'proof_info.json');info=read(evidence)
            tactics=[r for r in info['records'] if r.get('kind')=='tactic']
            if tactics and not info['unavailable_reason']:
                selected=max(tactics,key=lambda r:(r['end']-r['start'],-r.get('depth',0)));goals=selected.get('goals_after')
        a2='reject' if a1=='reject' else 'abstain' if a1=='abstain' else 'not_available' if goals is None else 'accept' if not goals else 'reject'
        if kind=='changed_statement':
            try:target.assert_statement(text);raise AssertionError('statement drift was not detected')
            except StatementMismatch as exc:
                result=VerificationResult(target.task_id,kind,sha(text),verifier.environment_id,'candidate','statement_mismatch',
                    statement_check='mismatch',detail=str(exc),failure_kind='statement_mismatch')
        else:
            result=verifier.verify(body,kind)
            if result.status=='candidate_pass':result=verifier.verify(body,kind+'_final','final')
        a3='accept' if result.status=='verified' else 'abstain' if result.status in ('timeout','environment_error','process_error','wall_time_limit') else 'reject'
        normalized='invalid_candidate' if result.status=='statement_mismatch' else result.status
        value=dict(problem=p,variant=kind,expected_valid=kind=='correct',expected_status=truth[kind],actual_status=result.status,
            expected_status_match=normalized==truth[kind],candidate_path=str(candidate),candidate_hash=sha(text),proof_sha256=sha(body),
            A1=a1,A2=a2,A3=a3,process=proc,A2_goals=goals,A2_selected_info=selected,A2_evidence=evidence,A3_result=result.to_dict())
        write(dest,value);log('V_A_case',problem=p,variant=kind,status=result.status,judges=[a1,a2,a3])

if __name__=='__main__':
    import argparse
    from concurrent.futures import ThreadPoolExecutor
    parser=argparse.ArgumentParser();parser.add_argument('--problems',type=int,nargs='+',default=list(range(1,16)));parser.add_argument('--workers',type=int,default=3);parser.add_argument('--variants',nargs='+',choices=VARIANTS,default=list(VARIANTS))
    args=parser.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for future in [pool.submit(execute,p,args.variants) for p in args.problems]:future.result()
