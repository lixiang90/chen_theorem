### Submission URL

https://github.com/lixiang90/chen_theorem/tree/a8d8292ba85931a416c44bc2a9be295b65966fda

### Model

OpenAI Codex (GPT-6 + GPT-5.6 Sol)

### Exact solution publication status

Public

### Publication date (if public)

2026-09-07

### Intended publication date (if planned)

_No response_

### How this solution was produced (optional)

Developed under human direction in OpenAI Codex using GPT-6 and GPT-5.6 Sol. This submission adapts the completed formalization at https://github.com/lixiang90/chen_theorem/tree/3264ad6acafa64ada18a309f48350d9acfd261ef and specializes its fixed-even-shift theorem to shift 2, proving the benchmark's exact prime-or-semiprime predicate.

The original Lean 4.32.2 project passed its full build and a transitive axiom audit of all 9,571 declarations across 415 local modules, allowing only propext, Classical.choice, and Quot.sound. The exact benchmark theorem bridge was also typechecked and axiom-audited against that proof. This submission uses the benchmark's fixed Lean 4.33.0 workspace; acceptance of this exact source snapshot is to be determined by the official comparator and nanoda checks.

All local helpers are included under Submission/. Prior work includes Mathlib and selected Apache-2.0 PNT, Mertens, and Perron proofs from PrimeNumberTheoremAnd commit c6c73610b406689c4b58325cbe1342ecca25d755, with notices and provenance retained. The sieve and Dirichlet zero-free-region proof chain, including the final ineffective real Siegel bound, is included locally. No first-proof or first-submission priority is claimed.

### Acknowledgements

- [x] I understand that the lean-eval CI will fetch my submission URL and run comparator on every lakefile.toml whose name matches a benchmark problem id.
- [x] I understand that only the set of solved problem IDs, along with the metadata I entered above, will be published to the public leaderboard results store.
- [x] I understand that an encrypted copy of the submission source tree (compressed gzipped tar, ≤ 10 MiB) is retained indefinitely in the private leanprover/lean-eval-audit repository for audit purposes, decryptable only by a small set of benchmark maintainers listed in .audit/recipients.txt. See https://github.com/leanprover/lean-eval-submissions/blob/main/docs/audit-archive.md.
