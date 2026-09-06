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
See [the current audit](formal/STATUS.md); the main theorem still has two
unproved mathematical inputs.

`formal/` is a Lake project targeting Lean `v4.32.2` / Mathlib `v4.32.2`. It
states every definition, lemma, and theorem of the paper in Lean. Lemmas 1, 2,
4, 5, and 7 are fully proved; the corrected height-logarithmic form of Lemma 3
is also proved and is sufficient for the later argument.  The Mertens theorem
and both prime-reciprocal partial-summation steps used in Lemma 8 have now been
proved in Lean using locally included Apache-2.0 analytic proofs, and the numerical integrals (24)
and (27) and inequality (28) are machine-checked without `sorryAx`.

Two explicit analytic trust-boundary declarations remain. Lemma 6 and its shifted
counterpart share a documented classical zero-free-region and `L'/L` estimate
proved by `sorry`; the original and fixed-shift forms of Lemma 9 are now both
instances of one parameterized Richert weighted-sieve/Bombieri--Vinogradov
interface.  The standalone development now proves the full level-`1/2`
Bombieri--Vinogradov statement.  It includes the exact character and primitive-
conductor reductions, Vaughan decomposition, Type-I and Type-II large-sieve
estimates, sharp hyperbola-boundary control, imprimitive-character errors,
finite-contour Siegel--Walfisz estimate, and final asymptotic parameter
assembly.  The theorem is conditional only on the same documented classical
zero-free-region package already used by Lemma 6; no additional axiom or
`sorry` was introduced.

The finite Rosser coefficients are now constructed. The original-variable
prime difference sequence and its middle-prime subsequences have exact
progression-error formulas, and the combined logarithmically weighted sieve
has BV remainder control without an extra divisor multiplicity. Ordinary-count
conversion now gives a finite bound for the exact counts in equation (26),
with explicit small-prime and non-reduced-class losses. The sieve product
also has the required singular-series normalization, using a locally included
proof of Mertens' third theorem and uniform divisor-tail control. All original
count-conversion and BV errors are now absorbed at arbitrary precision, with
explicit power sieve levels and valid middle-prime sublevels. The fixed-shift
construction, exact count conversion, singular-series normalization, and
error absorption are also proved. The quantitative dimension-one density
condition, nonnegative Rosser error recursions, and exact cumulative
Buchstab masses are now proved as well. Real-cutoff density bounds and weighted
Buchstab partial summation, with explicit error `2K f(z)/log w` under the stated
smoothness and logarithmic growth assumptions, are also proved. The logarithmic
parameter substitution and a Rosser recursion step now connect to the continuous
integral, retaining an explicit small-prime remainder that vanishes at each fixed
cutoff once the level is large enough. The continuous beta-two terms and their
finite odd/even delay system are now constructed, with positivity, continuity,
support and weighted monotonicity proved. Exact integral-mass identities now prove
convergence of both parity series, uniform convergence on the stated half-lines,
and the limiting delay equations. Both weighted errors now provably tend to zero,
and a conserved integral pairing proves the sharp lower endpoint value. The
constructed sieve functions have limits equal to one and the initial formulas
`F=A/s` and `f=A log(s-1)/s` on their stated intervals. The normalization
`A=2 exp γ` remains to be established. The actual error functions now give
concrete Rosser recursion steps, including the derivative joining point and
explicit density errors; the child-state induction hypotheses are retained.
The small-parameter upper case is now uniformly reduced to a local estimate at
a strict integer cube-root cutoff, whose parameter approaches three from above.
The actual defect now also has an exact decomposition by stopping depth, with
factorial tail control and an unconditional large-parameter bound. Comparison
now has a proved base case: the first depth term is uniformly bounded by its
continuous counterpart plus an arbitrarily small error. The parity structure
and the normalized depth recursion are also proved. The recursive continuous
terms now satisfy the Buchstab comparison across their derivative junctions,
using one-sided derivatives and retaining an explicit density error.
This now includes the first term. Additive errors in the discrete recursion
are controlled by the exact Buchstab tail mass, and a second-depth estimate
has been proved without child-state assumptions under explicit level conditions.
Choosing a growing split now yields the uniform second-depth bound by its
continuous counterpart plus an arbitrarily small error, for every terminal cutoff at least two.
For each higher upper depth, exact transport beyond the cube cutoff now
reduces its full parameter domain to the comparison above parameter three.
The general induction now proves comparison for every fixed positive depth
and every fixed finite sum of depths. A growing depth cutoff of order
`log log z` now leaves a uniformly vanishing remainder. Thresholds in the
fixed-depth comparison may depend on depth, so quantitative control of the
growing initial sum and sharp Rosser polynomial bounds in terms
of the linear-sieve functions and their final main-term combination are
still needed to remove the Lemma 9 axiom.
Auxiliary errors are now constructed from the continuous error derivatives,
with their initial formulas, continuity, weighted delay equations and
monotonicity proved. Their weighted tails vanish, yielding exact integral
identities and bounds. Weighted auxiliary integrals now control the exact
logarithmic error rescaling at child level `D/p`, with the weighted monotonicity
needed by Buchstab summation. One-sided derivatives through the auxiliary
junctions now yield discrete child-level error bounds with explicit terminal
density errors. Continuous partial sums now have uniform auxiliary majorants,
and cumulative discrete depth steps combine the main and auxiliary bounds with
constants independent of the cutoffs. The child induction hypotheses, small-prime
prefix and density errors remain explicit; completing the uniform induction is still open.
The actual continuous terms, errors and auxiliary functions are strictly positive
on their analytic domains. For each fixed parameter, weighted auxiliary integration
has a positive gap uniform in all sufficiently large upper endpoints. Quantitative
control of that gap as the parameter grows remains to be established.
Short-interval delay integrals now also give an explicit common lower bound
`c exp(-s log s - s log log s - 6s)` for both auxiliary functions at large
parameters, with `c>0` proved from their initial values. The quantitative
shift ratios and the remaining uniform discrete estimates are still open.
The additional factor `(1+s^d/log D)^s` now has a proved child-level
comparison and shifted derivative bound. Combining it with the auxiliary
lower bound gives an explicit lower bound for the full error scale; its
comparison with the discrete large-parameter remainder now has an explicit
exponential factor. The actual depth `floor(s)-2` gives an upper bound retaining
the term `-s log s`; comparing it with the full auxiliary lower bound gives
`defect ≤ exp(R) · auxiliary error`. A decreasing envelope now proves
`R≤-s` uniformly for `s≥σ(log D)` at sufficiently large levels, where
`σ(L)=L^(1/d) log L` and `d>2`. The rounded recursive prefix is now
controlled by `C(σ/s) exp(-σ) E(D,t)` with `t∈[σ,2σ]`, uniformly in
depth and the prime set. Later modules transfer the error from `t` to the
parent parameter and complete the middle-parameter comparison.
The auxiliary sum now has a proved vanishing integral pairing with the
polynomial `s²−2s+1/2`. Elementary shift bounds, fed back into this pairing,
prove `upper/lower auxiliary error ≤ C exp(-s)` for `s≥16`.
A second vanishing pairing and a maximum principle now prove uniform
comparison between the two auxiliary functions. Their cross-shift ratios
are reduced, with uniform constants, to the scalar ratio `Q(s−1)/(sQ(s))`.
An explicit exponential comparison and a first-stationary-point argument
now prove that the scalar ratio is eventually at least `(1/4) log s`;
both cross-shift ratios inherit uniform logarithmic lower bounds.
The matching logarithmic upper bound is now proved by the opposite
comparison function. Compactness extends both bounds uniformly to every
`s≥3`, including both cross-shift estimates. Uniform logarithmic control of
the inflation factor now proves that both inflated weighted errors decrease
on `[3,2σ(log D)]`, for every shift in `[0,1]`. This transfers the rounded
small-prime prefix to the parent parameter with bound `C exp(-σ) E(D,s)`,
uniform in cumulative depth and the prime set. The lower branch now extends
to its endpoint two. Initial formulas also complete the weighted child
monotonicity on both required domains (`t≥3` for the lower child, `t>2` for
the upper child), and give the ordinary monotonicity and logarithmic growth
conditions in the prime-size variable. Integrable one-sided product
derivatives now give the actual child-level error sums a bound by an
explicit inflated integral plus terminal density loss. The integral now has
a proved quantitative strict contraction: the parent error is multiplied by
`1−(1−δ)/(4B)`, uniformly through the growing interval. Both terminal density
losses and the small-prime prefix are now absorbed. The resulting active
step retains the strict factor `1−(1−δ)/(64σ)` at the actual parent cutoff
`z+1`, uniformly in both depths and in multipliers `M≥1`, under
`d>3`, `0≤δ<1`, and `3/d<1−δ`. The child bound is still an explicit
hypothesis. Passage to the full convergent continuous errors now gives the
same contracted step for the actual total Rosser defects. The stopped lower
branch is controlled by the proved identity `L(s)=2/s` for `0<s≤2`.
A common multiplier also controls every bounded child level, uniformly in
the cutoff and prime set. The initial upper interval is now absorbed into
the same error scale. Strong induction on the actual cutoff proves a uniform
total-defect bound with no child assumptions. Uniform vanishing of the error
on compact parameter intervals gives the actual Rosser polynomial bounds
`upper ≤ V(F+ε)` and `V(f−ε) ≤ lower`. The initial constant of these constructed
functions still needs to be identified with `2 exp γ` before the final
Chen weighted-sieve assembly can be completed.

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
