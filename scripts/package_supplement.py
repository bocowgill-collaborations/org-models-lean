#!/usr/bin/env python3
"""Package/verify the separately maintained fixed-input validation source archive."""
import argparse
import gzip
import hashlib
import io
import json
import re
import sys
import tarfile
from pathlib import Path

PREFIX = 'nk-r-validation-supplement'
ROOT_FILES = {'.gitignore', 'README.md', 'LICENSE', 'NOTICE', 'configure.py',
              'lean-toolchain', 'lakefile.template.toml', 'NKValidation.lean'}
ROLES = {'validation': {'fixtures.json', 'evaluate_sources.R'},
         'scripts': {'generate_fixtures.py', 'run_validation.py'},
         'docs': {'REFERENCE_VALIDATION.json', 'SOURCE_MANIFEST.json', 'SOURCE_CORRESPONDENCE.json'}}
HOME_PATH = re.compile('|'.join((re.escape('/'+'Users'+'/'), re.escape('/'+'home'+'/'),
                               re.escape('/private/var/'+'folders/'),
                               re.escape('/var/'+'folders/'), r'[A-Za-z]:\\'+'Users'+r'\\')))
REQUIRED = ROOT_FILES | {f'{folder}/{name}' for folder, names in ROLES.items() for name in names}
REQUIRED |= {'NKValidation/Fixtures.lean', 'NKValidation/Main.lean', 'NKValidation/Axioms.lean'}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def allowed(name):
    parts = Path(name).parts
    if len(parts) == 1:
        return name in ROOT_FILES
    if parts[0] == 'NKValidation':
        return name.endswith('.lean') and not any(p.startswith('.') for p in parts)
    return len(parts) == 2 and parts[0] in ROLES and parts[1] in ROLES[parts[0]]

def private_check(name, data):
    require(not HOME_PATH.search(data.decode('utf-8')), f'Personal filesystem path in {name}')

def package(source, output):
    require(source.is_dir() and not source.is_symlink(), 'Supply a real supplement source directory')
    payload = {}
    for folder in [*ROLES, 'NKValidation']:
        require((source / folder).is_dir() and not (source / folder).is_symlink(),
                f'Linked/missing source directory: {folder}')
    for name in sorted(ROOT_FILES):
        path = source / name
        require(path.is_file() and not path.is_symlink(), f'Missing/linked source: {name}')
        payload[name] = path.read_bytes()
    for folder, names in ROLES.items():
        for name in sorted(names):
            path = source / folder / name
            require(path.is_file() and not path.is_symlink(), f'Missing/linked source: {folder}/{name}')
            payload[f'{folder}/{name}'] = path.read_bytes()
    for path in sorted((source / 'NKValidation').rglob('*.lean')):
        require(not path.is_symlink() and path.resolve().is_relative_to(source.resolve()),
                'Linked or escaping Lean source')
        payload[path.relative_to(source).as_posix()] = path.read_bytes()
    for name, data in payload.items():
        require(allowed(name), f'Unexpected source role: {name}')
        private_check(name, data)
    require(REQUIRED <= payload.keys(), 'Missing required supplement source')
    manifest = {'schema_version': 1, 'artifact': PREFIX,
                'scope': 'First-party source and fixture data; originals and runtime outputs excluded',
                'files': {n: {'bytes': len(d), 'sha256': sha(d)} for n,d in sorted(payload.items())}}
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2, sort_keys=True)+'\n').encode()
    output.mkdir(parents=True, exist_ok=True)
    path = output / (PREFIX+'.tar.gz')
    with path.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as zipped:
            with tarfile.open(mode='w', fileobj=zipped, format=tarfile.USTAR_FORMAT) as archive:
                for name, data in sorted(payload.items()):
                    info = tarfile.TarInfo(PREFIX+'/'+name)
                    info.size, info.mtime, info.mode = len(data), 0, 0o644
                    archive.addfile(info, io.BytesIO(data))
    digest = sha(path.read_bytes())
    (output / (path.name+'.sha256')).write_text(f'{digest}  {path.name}\n')
    return {'status': 'packaged_locally', 'archive': path.name, 'sha256': digest,
            'bytes': path.stat().st_size, 'files': len(payload)}

def verify(path, destination=None):
    members = {}
    with tarfile.open(path) as archive:
        for item in archive.getmembers():
            parts = Path(item.name).parts
            require(item.isfile() and len(parts) >= 2 and parts[0] == PREFIX
                    and '..' not in parts and not Path(item.name).is_absolute(),
                    f'Unsafe member: {item.name}')
            name = Path(*parts[1:]).as_posix()
            require(name not in members, 'Duplicate archive member')
            require(name == 'MANIFEST.json' or allowed(name), f'Excluded source role: {name}')
            data = archive.extractfile(item).read()
            private_check(name, data)
            members[name] = data
    require('MANIFEST.json' in members, 'Missing manifest')
    manifest = json.loads(members['MANIFEST.json'])
    require(manifest['schema_version'] == 1 and manifest['artifact'] == PREFIX, 'Wrong archive schema')
    expected = manifest['files']
    require(set(members) == set(expected) | {'MANIFEST.json'}, 'File set differs from manifest')
    require(REQUIRED <= set(expected),
            'Manifest omits required supplement source')
    for name, record in expected.items():
        require(record == {'bytes': len(members[name]), 'sha256': sha(members[name])}, f'Corrupt content: {name}')
    if destination is not None:
        require(not destination.exists(), 'Extraction destination must be new')
        destination.mkdir(parents=True)
        for name, data in members.items():
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    return {'status': 'passed', 'files': len(members), 'sha256': sha(path.read_bytes())}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path)
    parser.add_argument('--output-dir', type=Path, default=Path('dist'))
    parser.add_argument('--verify', type=Path)
    parser.add_argument('--extract-to', type=Path)
    args = parser.parse_args()
    try:
        if args.verify:
            result = verify(args.verify, args.extract_to)
        else:
            require(args.source is not None and args.extract_to is None, 'Use --source or --verify')
            result = package(args.source, args.output_dir)
        print(json.dumps(result, indent=2))
    except (ValueError, OSError, KeyError, tarfile.TarError) as error:
        print(f'Supplement archive failed: {error}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
