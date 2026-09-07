# Chen theorem submission for LeanEval

Problem: `chen_theorem`, statement revision 1.

System: **OpenAI Codex (GPT-6 + GPT-5.6 Sol)**, under human direction.
This submission does not claim to be the first formalization or the first
accepted solution of this benchmark.

The proof is adapted from the completed project at
https://github.com/lixiang90/chen_theorem/tree/3264ad6acafa64ada18a309f48350d9acfd261ef
and specializes `Chen.chen_twin` to the shift 2. The adapter proves the exact
benchmark predicate `HasAtMostTwoPrimeFactors`; trusted challenge and bridge
files are copied unchanged from the benchmark snapshot in `PROVENANCE.json`.

Every local helper resides under `Submission/`. The only external proof-library
dependency is the benchmark's pinned Mathlib. The original project was fully
built with Lean 4.32.2, and its 9,571 declarations were audited to use only
`propext`, `Classical.choice`, and `Quot.sound`. The exact benchmark adapter was
also typechecked and axiom-audited against that original proof. The submitted
workspace targets the benchmark's Lean 4.33.0 and fixed Mathlib revision;
LeanEval's comparator and independent nanoda replay determine acceptance.

The development follows Chen's 1973 argument and includes locally copied
PNT/Mertens/Perron proofs from PrimeNumberTheoremAnd, commit
`c6c73610b406689c4b58325cbe1342ecca25d755`, with Apache-2.0 notices and provenance
preserved under `Submission/ChenTheorem/Analysis/PNT/`. Those included proofs
are credited as prior work, rather than claimed as newly generated.

To reproduce the evaluator environment, use the trusted generated workspace:

```text
lake update
lake build Solution
lake test
```

`lake test` requires the exact pinned landrun, lean4export, comparator, and
nanoda tools documented by https://github.com/leanprover/lean-eval.
The checker reconstructs trusted files from its own snapshot and overlays
only `Submission.lean` and `Submission/**/*.lean` from this repository.
