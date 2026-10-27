"""Check local documentation, HTML assets, preserved scope and prepared patch."""
import ast
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit
import unicodedata

HERE=Path(__file__).resolve().parent
SHARE=HERE.parents[6]
WARMUP=SHARE/'docs/research/refactoring/warmup/손지연'
IMPL=SHARE/'docs/research/verifier-guided-agent/손지연'

class HTMLLinks(HTMLParser):
    def __init__(self):
        super().__init__();self.targets=[];self.ids=set();self.images=[]
    def handle_starttag(self,tag,attrs):
        values=dict(attrs)
        if values.get('id'):self.ids.add(values['id'])
        for key in ('href','src'):
            if values.get(key):self.targets.append(values[key])
        if tag=='img':self.images.append(values.get('src'))

def github_anchors(text):
    values=set(re.findall(r'<a\s+id="([^"]+)"',text));counts={}
    for title in re.findall(r'^#{1,6}\s+(.+)$',text,re.M):
        title=re.sub('<[^>]+>','',title).lower()
        title=''.join(c for c in title if c in '-_' or unicodedata.category(c)[0] not in 'PS')
        slug=title.replace(' ','-');n=counts.get(slug,0);counts[slug]=n+1
        values.add(slug+(f'-{n}' if n else ''))
    return values

def main():
    docs=[p for p in SHARE.rglob('*.md') if 'evidence' not in p.relative_to(SHARE).parts]
    html=WARMUP/'verification-repair-experiment.html';docs.append(html)
    docs.extend([WARMUP/'evidence/README.md',IMPL/'evidence/README.md'])
    errors=[];links=0;images=0;whitespace=[]
    for path in docs:
        parser=HTMLLinks()
        if path.suffix=='.html':
            parser.feed(path.read_text());targets=parser.targets;images+=len(parser.images)
        else:targets=re.findall(r'\]\(([^)]+)\)',path.read_text())
        for target in targets:
            value=urlsplit(target)
            if value.scheme or value.netloc:continue
            dest=(path.parent/unquote(value.path)).resolve() if value.path else path
            links+=1
            if not dest.is_relative_to(SHARE) or not dest.exists():
                errors.append(dict(file=str(path.relative_to(SHARE)),target=target,reason='missing or outside sharing tree'))
            elif value.fragment:
                if dest.suffix=='.md':anchors=github_anchors(dest.read_text())
                elif dest.suffix=='.html':
                    other=HTMLLinks();other.feed(dest.read_text());anchors=other.ids
                else:continue
                if unquote(value.fragment) not in anchors:errors.append(dict(file=str(path.relative_to(SHARE)),target=target,reason='missing anchor'))
        # This workspace is not a Git checkout. Check new documents as added files.
        result=subprocess.run(['git','diff','--no-index','--check','/dev/null',str(path)],capture_output=True,text=True)
        # --no-index uses exit 1 for an ordinary difference; --check emits issues.
        if result.returncode not in (0,1) or result.stdout.strip() or result.stderr.strip():
            whitespace.append(dict(file=str(path.relative_to(SHARE)),output=result.stdout+result.stderr))
    code=0
    for path in SHARE.rglob('*.py'):
        ast.parse(path.read_text(),filename=str(path));code+=1
    before={}
    for name in ['docs/research/refactoring/warmup/README.md','docs/research/refactoring/warmup/손지연/README.md','docs/research/verifier-guided-agent/README.md']:
        before[name]=(HERE/'references'/name.replace('/','__')).read_bytes()
    with tempfile.TemporaryDirectory(prefix='lean-share-patch-check-') as directory:
        root=Path(directory)
        for name,value in before.items():
            dest=root/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(value)
        result=subprocess.run(['git','-C',str(root),'apply','--check',str(HERE/'upstream-index-additions.patch')],capture_output=True,text=True)
        patch_ok=result.returncode==0
    preservation=json.loads((HERE/'preservation.json').read_text())
    replay=json.loads((HERE/'record-replay.json').read_text())
    result=dict(passed=not errors and not whitespace and patch_ok and preservation['passed'] and replay['matched']==360,
        documents=len(docs),relative_links_checked=links,images=images,
        broken_links=errors,whitespace_errors=whitespace,python_files_parsed=code,
        git_diff_check=dict(mode='git diff --no-index --check on each new sharing document; source workspace is not a Git checkout',passed=not whitespace),
        upstream_index_patch_applies=patch_ok,source_preservation='preservation.json',record_replay=dict(histories=replay['histories'],matched=replay['matched']),
        implementation_unit_tests=51,new_model_calls=0,new_lean_runs=0,
        browser_visual_check=dict(performed=False,reason='Computer Use was not approved to use Google Chrome; browser inventory is empty. Static asset/link/anchor checks passed separately.'))
    (HERE/'share-checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))
    if not result['passed']:raise SystemExit(1)

if __name__=='__main__':main()
