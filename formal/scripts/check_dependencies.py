"""Check that mathlib is the only direct package dependency.

Run from formal/. Also rejects undeclared external module imports, including
accidental imports of the old PrimeNumberTheoremAnd checkout.
"""
from pathlib import Path
import json
import re
import tomllib

config = tomllib.loads(Path('lakefile.toml').read_text(encoding='utf-8'))
assert [p['name'] for p in config.get('require', [])] == ['mathlib']
manifest = json.loads(Path('lake-manifest.json').read_text(encoding='utf-8'))
mathlib = json.loads(Path('.lake/packages/mathlib/lake-manifest.json').read_text(encoding='utf-8'))
allowed = {'mathlib'} | {p['name'] for p in mathlib['packages']}
actual = {p['name'] for p in manifest['packages']}
assert actual == allowed, f'Unexpected package set: {actual ^ allowed}'

files = [Path('ChenTheorem.lean'), *Path('ChenTheorem').rglob('*.lean')]
for file in files:
    source = file.read_text(encoding='utf-8-sig')
    for imported in re.findall(r'^(?:public )?import\s+(\S+)', source, re.M):
        assert imported.split('.')[0] in {
            'ChenTheorem', 'Mathlib', 'Lean', 'Batteries', 'Aesop', 'Qq',
        }, f'{file}: external import {imported}'
        if imported.startswith('ChenTheorem.'):
            local = Path(*imported.split('.')).with_suffix('.lean')
            assert local.is_file(), f'{file}: missing local module {imported}'
print(f'PASS: {len(files)} source files; mathlib is the sole direct dependency; '
      f'{len(actual) - 1} standard mathlib transitive packages.')
