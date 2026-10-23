"""Summarize retained search evidence without changing candidate selection."""
import collections
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def main():
    by_operator={}; suggestion_categories=collections.Counter(); invocations=0
    for path in sorted((HERE/'runs').glob('*/*/result.json')):
        r=json.loads(path.read_text())
        for a in r['attempts']:
            counts=by_operator.setdefault(a['operator'],collections.Counter())
            counts['attempts']+=1;counts[a['outcome']]+=1
            if a['outcome']=='no_supported_suggestion':
                obs=a['query_observation'];p=Path(obs.get('output_path',''))
                if not p.is_file():p=path.parent/p.name
                output=p.read_text() if p.is_file() else ''
                category=('has_try_this_but_not_extracted' if 'Try this:' in output
                          else 'no_try_this_in_output')
                suggestion_categories[category]+=1
                counts['query_'+obs['kind']]+=1
    for path in (HERE/'runs').glob('*/*/*.run.json'):
        invocations+=1
    out={'operators':by_operator,'unsupported_suggestions':dict(suggestion_categories),
         'lean_invocations_with_record':invocations,
         'note':'Attempt counts use completed per-problem results; invocation count covers runs/ and excludes pilots, compatibility probes, and environment setup. A valid query is not an eligible explicit proof.'}
    (HERE/'diagnostics.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(out,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
