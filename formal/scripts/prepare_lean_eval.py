"""Package the proved Chen theorem for the pristine LeanEval chen_theorem workspace.

All helper imports move under Submission/. The benchmark's trusted files and
fixed dependency configuration are copied byte for byte, never rewritten.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--benchmark-dir', type=Path, required=True)
parser.add_argument('--output-dir', type=Path, required=True)
parser.add_argument('--source-rev', default='HEAD', help='Committed original proof revision')
parser.add_argument('--benchmark-rev', default='HEAD', help='Committed benchmark revision')
args = parser.parse_args()
formal = Path(__file__).resolve().parents[1]
benchmark = args.benchmark_dir.resolve()
output = args.output_dir.resolve()
output.mkdir(parents=True, exist_ok=True)


def committed_blobs(repository, paths, revision):
    refs = ''.join(f'{revision}:{path}\n' for path in paths)
    raw = subprocess.check_output(['git', '-C', str(repository), 'cat-file', '--batch'], input=refs.encode())
    stream = io.BytesIO(raw)
    result = {}
    for path in paths:
        header = stream.readline().split()
        assert len(header) == 3 and header[1] == b'blob', f'Not a committed source: {path}'
        result[path] = stream.read(int(header[2]))
        assert stream.read(1) == b'\n'
    return result

trusted = ['Challenge.lean', 'ChallengeDeps.lean', 'Solution.lean',
           'WorkspaceTest.lean', 'config.json', 'lakefile.toml', 'lean-toolchain']
trusted_blobs = committed_blobs(benchmark, [f'generated/chen_theorem/{name}' for name in trusted], args.benchmark_rev)
for name in trusted:
    (output / name).write_bytes(trusted_blobs[f'generated/chen_theorem/{name}'])

prefix = subprocess.check_output(['git', '-C', str(formal), 'rev-parse', '--show-prefix'], text=True).strip()
tracked = subprocess.check_output(
    ['git', '-C', str(formal), 'ls-tree', '-r', '--name-only', args.source_rev,
     '--', 'ChenTheorem.lean', 'ChenTheorem/'], text=True).splitlines()
sources = sorted(path for path in tracked if path.endswith('.lean'))
notices = ['ChenTheorem/Analysis/PNT/' + name for name in ['LICENSE', 'NOTICE', 'SOURCES.json']]
source_blobs = committed_blobs(formal, [prefix + path for path in sources + notices], args.source_rev)
hashes = {}
for source in sources:
    relative = Path(source)
    target = output / 'Submission' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    blob = source_blobs[prefix + relative.as_posix()]
    text = blob.decode('utf-8-sig')
    # The benchmark disables autoImplicit globally; preserve the original
    # modules' elaboration setting explicitly in the solver-owned sources.
    text = re.sub(r'^((?:public )?import\s+)(ChenTheorem(?:\.[\w.]+)?)\s*$',
                  r'\1Submission.\2', text, flags=re.M)
    lines = text.splitlines()
    last_import = max(i for i, line in enumerate(lines) if re.match(r'^(?:public )?import ', line))
    lines.insert(last_import + 1, '\nset_option autoImplicit true')
    target.write_text('\n'.join(line.rstrip() for line in lines).rstrip() + '\n', encoding='utf-8')
    hashes[relative.as_posix()] = hashlib.sha256(blob).hexdigest()

proof = '''import ChallengeDeps
import Submission.ChenTheorem.Main

namespace Submission

theorem chen_theorem :
    {p : ℕ | p.Prime ∧ LeanEval.NumberTheory.ChenTheorem.HasAtMostTwoPrimeFactors (p + 2)}.Infinite := by
  apply (Chen.chen_twin 2 (by decide) (by norm_num)).mono
  intro p hp
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with hprime | ⟨a, b, ha, hb, hab⟩
  · exact Or.inl ⟨p + 2, hprime, rfl⟩
  · exact Or.inr ⟨a, b, ha, hb, hab⟩

end Submission
'''
(output / 'Submission.lean').write_text(proof, encoding='utf-8')
for name in notices:
    (output / 'Submission' / name).write_bytes(source_blobs[prefix + name])
(output / '.gitignore').write_text('.lake/\n*.log\n*.olean\n*.ilean\n', encoding='utf-8')
metadata = {
    'source_repository': 'https://github.com/lixiang90/chen_theorem',
    'source_commit': subprocess.check_output(['git', '-C', str(formal), 'rev-parse', args.source_rev], text=True).strip(),
    'benchmark_commit': subprocess.check_output(['git', '-C', str(benchmark), 'rev-parse', args.benchmark_rev], text=True).strip(),
    'problem_id': 'chen_theorem',
    'declared_system': 'OpenAI Codex (GPT-6 + GPT-5.6 Sol)',
    'source_sha256': hashes,
    'trusted_sha256': {name: hashlib.sha256(trusted_blobs[f'generated/chen_theorem/{name}']).hexdigest() for name in trusted},
}
(output / 'PROVENANCE.json').write_text(json.dumps(metadata, indent=2) + '\n', encoding='utf-8')
print(f'Prepared {len(sources)} local proof modules and the theorem bridge in {output}')
