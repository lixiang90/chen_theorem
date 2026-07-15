# Chen's Theorem (1 + 2)

A LaTeX transcription (Chinese original + English translation) and a Lean 4 /
Mathlib formalization skeleton of Chen Jingrun's landmark 1973 paper:

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
| [`formal/`](formal) | A Lean 4 / Mathlib formalization skeleton — see [`formal/README.md`](formal/README.md) for full details |

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

`formal/` is a Lake project targeting Lean `v4.31.0` / Mathlib `v4.31.0`. It
states every definition, lemma, and theorem of the paper in Lean, and
**Lemma 1 (the smoothing-function estimate) and Lemma 4 (the primitive-character
sum bound) are fully proved**, with no `sorry`. The remaining lemmas and the main
theorems are stated precisely but not yet proved. See [`formal/README.md`](formal/README.md) for the build
instructions, the full correspondence table against the paper, and design
notes.

```
cd formal
lake exe cache get
lake build
```
