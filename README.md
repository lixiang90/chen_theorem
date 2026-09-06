# Chen's Theorem (1 + 2)

A LaTeX transcription (Chinese original + English translation) and an
in-progress Lean 4 / Mathlib formalization of Chen Jingrun's landmark 1973
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

The only direct Lake dependency is Mathlib. Necessary PNT/Mertens/Perron
proofs are included as project sources with their original license and provenance.
See [the current audit](formal/STATUS.md); the main theorem still has one
unproved mathematical input, the primitive Dirichlet zero-free-region package.

`formal/` is a Lake project targeting Lean `v4.32.2` / Mathlib `v4.32.2`. It
states every definition, lemma, and theorem of the paper in Lean. Lemmas 1, 2,
4, 5, and 7 are fully proved; the corrected height-logarithmic form of Lemma 3
is also proved and is sufficient for the later argument.  The Mertens theorem
and both prime-reciprocal partial-summation steps used in Lemma 8 have now been
proved in Lean using locally included Apache-2.0 analytic proofs, and the numerical integrals (24)
and (27) and inequality (28) are machine-checked without `sorryAx`.

One unproved analytic input remains: `primitive_zero_free_region` supplies the
height-dependent Dirichlet zero-free region and Siegel bounds. The companion
logarithmic-derivative estimate is now proved from nonvanishing in that mixed
region. Lemma 6 and the standalone level-`1/2`
Bombieri--Vinogradov theorem both depend on this documented `sorry`.

The extra `richert_bombieri_equation26` axiom has been replaced by a theorem
with the same statement. Its proof constructs finite Rosser weights, proves
uniform discrete-to-continuous error bounds, calibrates the linear-sieve
constant as `2 exp γ`, and computes the continuous profile in equation (26).
Mertens/Abel summation now evaluates the actual `1/φ(p)`-weighted middle-prime
sum. Uniform control of rounded parent and child levels transfers the
continuous bounds to the actual polynomials. Combining these with the sieve
product normalization and the proved BV remainder/count-conversion bounds
establishes equation (26) for both original and fixed-shift families.

The new sieve and parameter-assembly proofs introduce no mathematical axioms.
The main theorems still inherit `sorryAx` from the single zero-free-region
gap, so this project is not yet a completed unconditional formalization. The remaining
analysis now derives the full half-width logarithmic-derivative estimate
from mixed-region nonvanishing, using disk geometry, Euler/Möbius bounds,
and explicit conductor-height estimates. Compact local zero-free strips and
the classical three-four-one logarithmic-derivative inequality are also proved.
Finite zero factorization now yields a primitive L-function local zero-pole
expansion with an absolute conductor-height logarithmic error bound.
The uniform logarithmic zero-free region is now proved for primitive characters
with nonprincipal square. Exact change-of-level derivative formulas control
imprimitive Euler factors, and the original remaining goal is reduced to
primitive real characters. Their nonexceptional region and Siegel estimates
remain unproved.
For primitive real characters, conjugate-zero pairing now proves that any
zero in a uniform box of width and height `c/log(2q)` around 1 must be real;
any such zero is now also proved unique and simple in a uniform smaller box.
The possible exceptional real zero is not excluded, and its Siegel distance
bound remains unproved.

The remaining deductions in the fixed-shift chain are explicit: the parallel Lemmas 1--9, the
shifted combinatorial inequality (28), the numerical `0.67` deduction, and the
passage from even auxiliary scales to every sufficiently large scale are all
machine-checked.  In particular the former aggregate `sorry` in
`chenCountShift_lower_estimate` has been removed.  The final numerical
deduction and representation extraction for Theorem 1, and the infinitude
deduction for Theorem 2, are proved from the
named upstream estimates in `Main.lean`. See
[`formal/README.md`](formal/README.md) for the build instructions, the full
correspondence table, and design notes.

```
cd formal
lake exe cache get
lake build
```
