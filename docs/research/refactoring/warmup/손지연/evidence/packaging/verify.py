"""Verify published plain and compressed payloads against the source inventory."""
import gzip
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    records = json.loads((HERE / 'included-files.json').read_text())
    provenance = json.loads((HERE / 'provenance.json').read_text())
    original = {row['destination']: row for row in map(json.loads,
        gzip.decompress((HERE / 'copy-manifest.jsonl.gz').read_bytes()).decode().splitlines())}
    errors = []
    archives = {}
    for record in records:
        source = record['source'].removeprefix('share/')
        if source in original and record['sha256'] != original[source]['sha256']:
            errors.append(f'Source inventory mismatch: {source}')
        expected = record.get('published_sha256', record['sha256'])
        if 'file' in record:
            actual = sha((ROOT / record['file']).read_bytes())
        elif 'gzip' in record:
            actual = sha(gzip.decompress((ROOT / record['gzip']).read_bytes()))
        else:
            archives.setdefault(record['archive'], {})[record['member']] = expected
            continue
        if actual != expected:
            errors.append(f'Payload mismatch: {source}')
    for archive, members in archives.items():
        archive_path = ROOT / archive
        if sha(archive_path.read_bytes()) != provenance['archive_sha256']:
            errors.append(f'Archive hash mismatch: {archive}')
        seen = set()
        with tarfile.open(archive_path, 'r:gz') as stream:
            for member in stream:
                if member.name in seen or member.name not in members or not member.isfile():
                    errors.append(f'Unexpected archive entry: {member.name}')
                    continue
                seen.add(member.name)
                if sha(stream.extractfile(member).read()) != members[member.name]:
                    errors.append(f'Archive payload mismatch: {member.name}')
        if seen != set(members):
            errors.append(f'Archive file set mismatch: {archive}')
    result = dict(passed=not errors, source_files_checked=len(records),
                  archived_files_checked=sum(map(len, archives.values())),
                  original_inventory_files=len(original), errors=errors)
    print(json.dumps(result, ensure_ascii=False))
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
