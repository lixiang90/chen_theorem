# Chen's Theorem (1 + 2)

A LaTeX transcription (Chinese original + English translation) and an
Lean 4 / Mathlib formalization of Chen Jingrun's landmark 1973
paper:

> 陈景润, 《大偶数表为一个素数及一个不超过二个素数的乘积之和》, 中国科学 **16** (1973), 111–128.
>
> Chen Jingrun, *On the representation of a large even integer as the sum of a
> prime and the product of at most two primes*, Sci. Sinica **16** (1973), 111–128.

This is the paper proving the celebrated **"1 + 2" theorem**: every sufficiently
large even integer is the sum of a prime and a number that is either prime or
the product of two primes — the closest result to date to the Goldbach
conjecture and the twin prime conjecture, obtained via a refinement of the
linear sieve.

## Contents

| Directory | Contents |
|---|---|
| [`pages/`](pages) | Page scans (`page-01.png` … `page-18.png`) of the original journal article, pp. 111–128 |
| [`pdf/`](pdf) | The original scanned PDF, plus compiled PDFs of the Chinese and English transcriptions |
| [`latex/`](latex) | LaTeX sources: `main.tex`/`part{1,2,3}.tex` (Chinese, faithful transcription) and `main_en.tex`/`part{1,2,3}_en.tex` (English translation), sharing the same equation numbering |
| [`formal/`](formal) | A Lean 4 / Mathlib formalization — see [`formal/README.md`](formal/README.md) for full details |

## Building the LaTeX

Requires a TeX distribution with `xelatex` and the `ctex` package (for the
Chinese document).

```
cd latex
xelatex main.tex      # Chinese transcription -> main.pdf
xelatex main_en.tex   # English translation    -> main_en.pdf
```

Each may need to be run twice to resolve cross-references.

## The Lean formalization

`formal/` targets Lean `v4.32.2` / Mathlib `v4.32.2`. It proves Chen's theorem,
its fixed even-shift analogue, and both quantitative counting bounds. The
original main theorem statements are unchanged. See the [formalization audit](formal/STATUS.md)
for the proof history and kernel checks.

Mathlib is the only direct Lake dependency. The necessary PNT, Mertens and
Perron proofs are included locally, with their Apache-2.0 license and pinned
source provenance. Building does not use a linked `PrimeNumberTheoremAnd` checkout.

The final analytic input, Siegel's ineffective real zero-free region, is now
proved using the positive four-L-function product, its regularized Taylor
series, small-power bounds near one, and two-character zero repulsion.
Together with the logarithmic nonexceptional region this completes the
zero-free-region package used by Lemma 6 and Bombieri–Vinogradov.

The Richert–Bombieri sieve axiom has also been replaced by a proof with the
same statement: finite Rosser weights, uniform discrete-to-continuous bounds,
the `2 exp(γ)` calibration, actual weighted prime sums, and rounded sieve levels.
There are no remaining proof placeholders or added mathematical axioms.

The formalization uses a corrected height-logarithmic version of the paper's
Lemma 3 and the asymptotic strength of equation (25) needed for the conclusion;
it does not claim the stronger printed intermediate estimates. See
[the correspondence and design notes](formal/README.md).

```text
cd formal
lake exe cache get
python scripts/check_dependencies.py
lake build
lake env lean AuditAnalysis.lean
lake env lean AuditSieve.lean
lake env lean Audit.lean
lake env lean AuditAll.lean
```

The audits accept only `propext`, `Classical.choice`, and `Quot.sound`.
The final audit checks the actual main theorem proof terms transitively.

Validation: the full build passes; all 9,571 declarations in the 415 local
modules pass the axiom audit. The focused analysis, sieve and main-theorem
audits pass 249, 930 and 12 checks respectively.
