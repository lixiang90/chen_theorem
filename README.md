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

`formal/` is a Lake project targeting Lean `v4.32.2` / Mathlib `v4.32.2`. It
states every definition, lemma, and theorem of the paper in Lean. Lemmas 1, 2,
4, 5, and 7 are fully proved; the corrected height-logarithmic form of Lemma 3
is also proved and is sufficient for the later argument.  The Mertens theorem
and both prime-reciprocal partial-summation steps used in Lemma 8 have now been
proved in Lean from `PrimeNumberTheoremAnd`, and the numerical integrals (24)
and (27) and inequality (28) are machine-checked without `sorryAx`.

Three explicit analytic trust boundaries remain. Lemma 6 and its shifted
counterpart share a documented classical zero-free-region and `L'/L` estimate
proved by `sorry`; the original and fixed-shift forms of Lemma 9 each depend on
a named Richert weighted-sieve/Bombieri--Vinogradov specialization.  Everything
else in the fixed-shift chain is now explicit: the parallel Lemmas 1--9, the
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
