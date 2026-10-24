"""Check published Week 4 navigation, local assets, anchors, and Python syntax."""
import ast
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import unicodedata
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
WARMUP = ROOT / 'docs/research/refactoring/warmup/손지연'
IMPL = ROOT / 'docs/research/verifier-guided-agent/손지연'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.targets = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if values.get('id'):
            self.ids.add(values['id'])
        self.targets.extend(values[key] for key in ('href', 'src') if values.get(key))


def anchors(path):
    text = path.read_text()
    if path.suffix == '.html':
        parser = Links()
        parser.feed(text)
        return parser.ids
    result = set(re.findall(r'<a\s+id="([^"]+)"', text))
    counts = {}
    for title in re.findall(r'^#{1,6}\s+(.+)$', text, re.M):
        title = re.sub('<[^>]+>', '', title).lower()
        title = ''.join(c for c in title if c in '-_' or unicodedata.category(c)[0] not in 'PS')
        slug = title.replace(' ', '-')
        count = counts.get(slug, 0)
        counts[slug] = count + 1
        result.add(slug + (f'-{count}' if count else ''))
    return result


def main():
    documents = [ROOT / name for name in (
        'docs/README.md', 'docs/research/README.md',
        'docs/research/refactoring/README.md', 'docs/research/refactoring/warmup/README.md',
        'docs/research/verifier-guided-agent/README.md',
        'docs/meetings/2026-10-25-week4/README.md')]
    documents += [WARMUP / name for name in (
        'README.md', 'verification-repair-experiment.md',
        'verification-repair-experiment.html', 'evidence/README.md')]
    documents += [IMPL / name for name in ('README.md', 'report.md', 'evidence/README.md')]
    errors = []
    checked = 0
    for path in documents:
        if path.suffix == '.html':
            parser = Links()
            parser.feed(path.read_text())
            targets = parser.targets
        else:
            targets = re.findall(r'\]\(([^)]+)\)', path.read_text())
        for target in targets:
            value = urlsplit(target)
            if value.scheme or value.netloc:
                continue
            checked += 1
            destination = (path.parent / unquote(value.path)).resolve() if value.path else path
            reason = None
            if not destination.is_relative_to(ROOT) or not destination.exists():
                reason = 'missing or outside repository'
            elif value.fragment and destination.suffix in ('.md', '.html'):
                if unquote(value.fragment) not in anchors(destination):
                    reason = 'missing anchor'
            if reason:
                errors.append(dict(file=str(path.relative_to(ROOT)), target=target, reason=reason))
    python_files = 0
    svg_files = 0
    for root in (WARMUP / 'evidence', IMPL / 'evidence'):
        for path in root.rglob('*.py'):
            ast.parse(path.read_text(), filename=str(path))
            python_files += 1
        for path in root.rglob('*.svg'):
            ET.parse(path)
            svg_files += 1
    result = dict(passed=not errors, documents=len(documents), relative_links_checked=checked,
                  python_files_parsed=python_files, svg_files_parsed=svg_files, errors=errors)
    print(json.dumps(result, ensure_ascii=False))
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
