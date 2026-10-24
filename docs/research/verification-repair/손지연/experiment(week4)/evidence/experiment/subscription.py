"""Text-only subscription transport; no API keys, credits, tools or fallback."""
import json
import re
import tempfile
from pathlib import Path
from common import write, sha
from lean_repair.model import ModelError
from quota import read_quota, check_included_quota

def redact(value):
    if isinstance(value,str):return re.sub(r'/Users/[^\s\"\']+','<local-path>',value)
    if isinstance(value,dict):return {k:redact(v) for k,v in value.items()}
    if isinstance(value,list):return [redact(v) for v in value]
    return value

class Budget:
    def __init__(self,path,max_calls,max_tokens=240000):
        self.path=Path(path)
        if self.path.exists():raise ValueError('Refusing to overwrite a model ledger')
        self.max_calls,self.max_tokens=max_calls,max_tokens
        self.calls=self.tokens=0;self.uncertain=False;self.entries=[];self.quota=None
    def snapshot(self):
        return dict(calls=self.calls,tokens=self.tokens,max_calls=self.max_calls,max_model_tokens=self.max_tokens,
            accounting_uncertain=self.uncertain,billing='ChatGPT subscription',api_spend_usd=None,quota=self.quota)
    def save(self):write(self.path,dict(snapshot=self.snapshot(),entries=self.entries))
    def reserve_tokens(self,prompt):return len(prompt.encode())//3+16000
    def can_reserve(self,amount):return not self.uncertain and self.calls<self.max_calls and self.tokens+amount<=self.max_tokens

class CodexModel:
    def __init__(self,runner,model='gpt-5.6-sol'):self.runner,self.model=runner,model
    def propose(self,payload,directory,timeout,budget):
        directory=Path(directory);directory.mkdir(parents=True)
        payload=redact(payload)
        write(directory/'request.json',payload)
        schema={'type':'object','properties':{k:{'type':'string'} for k in ('diagnosis','proof_body')},
            'required':['diagnosis','proof_body'],'additionalProperties':False}
        write(directory/'schema.json',schema)
        prompt=('Text-only Lean 4 experiment. Do not use tools, files, browsing, search, or delegation. '
            'Use ONLY the supplied context. Return diagnosis and proof_body as JSON strings. '
            'proof_body must be a complete by proof.\n'+json.dumps(payload,ensure_ascii=False))
        write(directory/'prompt_manifest.json',dict(sha256=sha(prompt),utf8_bytes=len(prompt.encode()),
            model=self.model,reasoning='high',api_spend_usd=None))
        if budget.uncertain:raise ModelError('subscription_accounting_uncertain')
        if budget.calls>=budget.max_calls:raise ModelError('subscription_call_limit')
        estimate=budget.reserve_tokens(prompt)
        if not budget.can_reserve(estimate):raise ModelError('subscription_token_reservation_limit')
        try:quota=read_quota(timeout=min(30,timeout))
        except (OSError,RuntimeError,TimeoutError):raise ModelError('subscription_quota_unavailable') from None
        write(directory/'quota_before.json',quota);budget.quota=quota
        if not check_included_quota(quota):budget.save();raise ModelError('subscription_included_quota_limit')
        budget.calls+=1;budget.uncertain=True
        entry=dict(call=budget.calls,state='in_flight',estimated_reserved_tokens=estimate,api_spend_usd=None)
        budget.entries.append(entry);budget.save()
        argv=['codex','exec','--ignore-user-config','--skip-git-repo-check','--ephemeral','--sandbox','read-only',
            '--json','--color','never','--model',self.model,'-c','forced_login_method="chatgpt"',
            '-c','model_reasoning_effort="high"','-c','features.shell_tool=false','-c','features.unified_exec=false',
            '-c','features.multi_agent=false','-c','features.apps=false','-c','features.plugins=false',
            '-c','features.skill_search=false','-c','features.hooks=false','-c','web_search="disabled"',
            '-c','project_doc_max_bytes=0','-c','developer_instructions=""','--output-schema',str(directory/'schema.json'),
            '--output-last-message',str(directory/'response.json'),'-']
        cwd=Path(tempfile.gettempdir())/'week4-lean-subscription-workdir';cwd.mkdir(exist_ok=True)
        proc=self.runner.run(argv,cwd,directory/'process',timeout,stdin=prompt)
        events=[]
        for line in Path(proc['stdout']).read_text(errors='replace').splitlines():
            try:events.append(json.loads(line))
            except ValueError:pass
        completed=[e for e in events if e.get('type')=='turn.completed']
        usage=completed[-1].get('usage') if completed else None
        tools=[e for e in events if e.get('type')=='item.completed' and e.get('item',{}).get('type') not in ('agent_message','reasoning')]
        entry.update(process=proc,usage=usage,tool_events=tools)
        if usage and all(type(usage.get(k)) is int for k in ('input_tokens','output_tokens')):
            budget.tokens+=usage['input_tokens']+usage['output_tokens'];budget.uncertain=False;entry['state']='completed'
        else:entry['state']='unknown_usage'
        budget.save()
        if proc['timeout'] or proc['wall_time_limit']:raise ModelError('subscription_timeout')
        if proc['returncode']!=0 or not completed:raise ModelError('subscription_failed')
        if tools:raise ModelError('experiment_tool_use_violation')
        if budget.tokens>budget.max_tokens:raise ModelError('subscription_token_limit')
        try:
            proposal=json.loads((directory/'response.json').read_text())
            if set(proposal)!={'diagnosis','proof_body'} or not all(isinstance(v,str) for v in proposal.values()):raise ValueError()
        except (OSError,ValueError,TypeError):raise ModelError('invalid_model_output') from None
        return proposal
