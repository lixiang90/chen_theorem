"""Extract the PNT lemmas used by Chen, without upstream blueprint tooling.

Run from formal/. The pinned upstream checkout is needed only to regenerate
these files; it is not needed to build them.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

SOURCE = Path('.lake/packages/PrimeNumberTheoremAnd')
DEST = Path('ChenTheorem/Analysis/PNT')
PREFIX = 'PrimeNumberTheoremAnd.'
LOCAL = 'ChenTheorem.Analysis.PNT.'
COMMIT = 'c6c73610b406689c4b58325cbe1342ecca25d755'

revision = subprocess.check_output(
    ['git', '-C', str(SOURCE), 'rev-parse', 'HEAD'], text=True).strip()
if revision != COMMIT:
    raise SystemExit(f'Expected upstream {COMMIT}, found {revision}')
dirty = subprocess.check_output(
    ['git', '-C', str(SOURCE), 'status', '--porcelain', '--untracked-files=no'],
    text=True).strip()
if dirty:
    raise SystemExit('Upstream has tracked modifications; refusing incorrect provenance')


def strip_blueprints(s):
    # Balanced attributes, respecting nested Lean comments and quoted strings.
    while (match := re.search(r'@\[blueprint\b', s)) is not None:
        start = match.start()
        i, depth, comment, quoted = start + 2, 1, 0, False
        while depth:
            if comment:
                if s.startswith('/-', i):
                    comment += 1
                    i += 2
                elif s.startswith('-/', i):
                    comment -= 1
                    i += 2
                else:
                    i += 1
            elif quoted:
                if s[i] == '\\':
                    i += 2
                elif s[i] == '"':
                    quoted = False
                    i += 1
                else:
                    i += 1
            elif s.startswith('/-', i):
                comment = 1
                i += 2
            elif s.startswith('--', i):
                i = s.index('\n', i)
            else:
                if s[i] == '"':
                    quoted = True
                elif s[i] == '[':
                    depth += 1
                elif s[i] == ']':
                    depth -= 1
                i += 1
        s = s[:start] + s[i:]
    s = re.sub(r'blueprint_comment\s+/--', '/-', s)
    # Architect extends tactic syntax with proof docstrings. Ordinary Lean
    # comments preserve their text without depending on that extension.
    s = s.replace('/--', '/-')
    s = re.sub(r'^import Architect\s*$', '', s, flags=re.M)
    s = re.sub(r'^#print axioms .*\n?', '', s, flags=re.M)
    return s


manifest = []
seen = set()


def extract(module):
    if module in seen:
        return
    seen.add(module)
    relative = Path(*module.split('.')).with_suffix('.lean')
    raw = (SOURCE / 'PrimeNumberTheoremAnd' / relative).read_bytes()
    s = raw.decode('utf-8-sig')
    if module == 'IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime':
        # Only the proof through Mertens' second theorem is used. The rest
        # includes numerical bounds and an unrelated unproved theorem.
        end = s.index('\n@[blueprint', s.index('theorem mertens_second_theorem :'))
        s = s[:end] + '\n\nend RS_prime\n'
        s = re.sub(r'^import PrimeNumberTheoremAnd.IEANTN.(SecondaryDefinitions|RosserSchoenfeld.RosserSchoenfeldPrime_tables)\s*$', '', s, flags=re.M)
        # This prime-counting identity is unused by Mertens and relied on
        # the secondary-definitions module's alternative pi notation.
        s = re.sub(r'theorem eq_417\b.*?(?=@\[blueprint|theorem eq_418)', '', s, flags=re.S)
        s = re.sub(r'(rw \[leftLim_theta_succ\]\s+)simp \[Real.log_nonneg\]',
                   r'\1simp [Real.log_nonneg, Nat.prime_two]', s)
    if module == 'Tactic.AdditiveCombination':
        # Keep the documentation example with local hypotheses rather than
        # the upstream snippet's global axiom declarations (inside a comment).
        s = s.replace('axiom qc : ℚ\naxiom hqc : qc = 2*qc\n\nexample (a b : ℚ)',
                      'example (qc : ℚ) (hqc : qc = 2*qc) (a b : ℚ)')
    if module == 'PerronFormula':
        # No declaration from Wiener is used by the Perron proof.
        s = s.replace('import PrimeNumberTheoremAnd.Wiener',
            'import Batteries.Tactic.Lemma\n'
            'import Mathlib.MeasureTheory.Integral.IntegralEqImproper\n'
            'import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals')
    s = strip_blueprints(s)
    for imp in re.findall(r'^import\s+(\S+)', s, re.M):
        if imp.startswith(PREFIX):
            extract(imp.removeprefix(PREFIX))
        elif not imp.startswith(('Mathlib.', 'Batteries.', 'Lean')):
            raise ValueError(f'Unexpected dependency: {imp}')
    s = re.sub(r'(?m)^(import\s+)PrimeNumberTheoremAnd\.', r'\1' + LOCAL, s)
    # The source occasionally documents abandoned proofs in line comments.
    s = re.sub(r'^--[^\n]*\bsorry\b[^\n]*\n?', '', s, flags=re.M)
    s = re.sub(r'\n{4,}', '\n\n\n', s)
    header = (f'/-\nAdapted from PrimeNumberTheoremAnd/{relative.as_posix()}\n'
              f'Upstream commit: {COMMIT}\n'
              'License: Apache-2.0; see LICENSE and NOTICE in this directory tree.\n'
              'Blueprint annotations removed; imports localized. See SOURCES.json.\n-/\n')
    target = DEST / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    generated = header + s
    # Avoid rewriting unchanged sources (and needless downstream rebuilds).
    if not target.exists() or target.read_text(encoding='utf-8') != generated:
        target.write_text(generated, encoding='utf-8')
    manifest.append({'module': module, 'source_sha256': hashlib.sha256(raw).hexdigest(),
                     'source_lines': len(raw.splitlines()),
                     'local_lines': len((header + s).splitlines())})


for seed in ['MediumPNT', 'PerronFormula', 'IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime',
             'IEANTN.Mertens']:
    extract(seed)
shutil.copyfile(SOURCE / 'LICENSE', DEST / 'LICENSE')
(DEST / 'SOURCES.json').write_text(json.dumps({
    'repository': 'https://github.com/AlexKontorovich/PrimeNumberTheoremAnd',
    'commit': COMMIT, 'files': manifest}, indent=2) + '\n', encoding='utf-8')
(DEST / 'NOTICE').write_text(
    'This directory contains adapted portions of PrimeNumberTheoremAnd.\n'
    'Upstream: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd\n'
    f'Commit: {COMMIT}\nLicense: Apache-2.0 (LICENSE).\n'
    'Original authorship and copyright notices in source files are retained.\n'
    'Modifications: removed blueprint annotations and Architect imports;\n'
    'localized imports; excluded unused Wiener and numerical-table imports;\n'
    'retained RosserSchoenfeldPrime only through Mertens second theorem.\n'
    'Further local proof/import changes are tracked in the project history.\n', encoding='utf-8')
print(f'Extracted {len(manifest)} modules ({sum(f["local_lines"] for f in manifest)} lines).')
