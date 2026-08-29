# Formal skeleton of Chen's theorem (1 + 2) in Lean 4 / Mathlib

This is a Lake project giving a **formal skeleton** — precise Lean statements with
`sorry` proofs — of Chen Jingrun's 1973 paper

> Chen Jingrun, *On the representation of a large even integer as the sum of a
> prime and the product of at most two primes*, Sci. Sinica **16** (1973), 111–128.

(A LaTeX transcription of the paper, in Chinese and English, lives in the parent
directory: `../latex/main.tex`, `../latex/main_en.tex`.)

- **Lean**: `leanprover/lean4:v4.32.1`
- **Mathlib**: release tag `v4.32.1`

## Build

```
cd formal
lake exe cache get   # download prebuilt Mathlib binaries
lake build
```

## Structure

| File | Contents |
|---|---|
| `ChenTheorem/Defs.lean` | All definitions: `IsP2`, counting functions `P_x(1,2)`/`x_h(1,2)`, singular series `C_x`, smoothing function `Φ`, sieve weights `λ_d`, the sums `Ω`, `M₁`, and the sifted prime counts of Lemma 9 |
| `ChenTheorem/LargeSieve/Gallagher.lean` | Centered-interval Sobolev/Gallagher inequality |
| `ChenTheorem/LargeSieve/Additive.lean` | Parseval, Farey spacing, and the additive large sieve |
| `ChenTheorem/LargeSieve/Character.lean` | Gauss-sum transition, character large sieve (2), and dyadic form (3) |
| `ChenTheorem/SieveLemmas.lean` | Lemmas 1–4: properties of `Φ`, the large sieve, the `L`-function fourth moment, primitive character sums |
| `ChenTheorem/Lemma5/Core.lean` | Finite-sum definitions and elementary reductions used in Lemma 5 |
| `ChenTheorem/Lemma5/{Arithmetic,Smoothing}.lean` | Arithmetic majorants, formula (5), and the small-base transition estimate |
| `ChenTheorem/Lemma5/{PrimeReciprocals,EulerPenalty}.lean` | Prime reciprocal estimates and the Euler-factor penalty for excluded prime divisors |
| `ChenTheorem/Lemma5/Boundary/{Sieve,Selberg,Weights,Mass,Analytic}.lean` | The dimension-two boundary sieve, Selberg diagonalization and optimal weights, the lower bound for `G(R)`, and the final short-interval estimate |
| `ChenTheorem/Lemma6/FourthMoment.lean` | The dyadic, totient-weighted `L'` fourth moment required after equation (15), with one rigorous logarithmic slack over the paper's displayed exponent, explicitly derived from the corrected Lemma 3 interface |
| `ChenTheorem/Lemma6/{PairBlockEstimate,LargePairBlock}.lean` | The full dyadic-block analysis of equations (13)–(20): block-summed A/B contour bounds, the remainder majorant scale bounds, and the pointwise regime estimates closing each occupied `(l,k)` block by `O(x/(log x)^20)` |
| `ChenTheorem/Lemma6/ZeroFreeRegion.lean` | The classical zero-free region for primitive `L(s,χ)` with the companion `L'/L` bound, recorded as the honest unproved interface `PrimitiveZeroFreeRegion` (the single intentional `sorry` of Lemma 6) |
| `ChenTheorem/Lemma6/Equation21.lean` | The complete equation-(21) pipeline from that interface: the unsplit logarithmic-derivative integrand, holomorphy inside the region, Cauchy–Goursat on `[1-1/√(log x), α]` rectangles, horizontal-edge decay from the kernel's half-power decay, and the final character-level bound `≪ (log x)^90 · Σ (x/p₁p₂)^{1-1/√(log x)}` |
| `ChenTheorem/Lemma6/Core.lean` | The finite `N_m`, its small/large-conductor split, equations (12)–(21), and the proved final logarithmic deduction for Lemma 6 |
| `ChenTheorem/Main/NumericalBounds.lean` | Independent, `sorry`-free analytic proofs of the numerical integral bounds (24) and (27), with exact rational remainder estimates |
| `ChenTheorem/MainEstimates.lean` | Lemmas 5–9: the sieve decomposition, `M₁ ≤ …`, `Ω ≤ 3.9404 xC_x/(log x)²`, the Richert-sieve lower bound `≥ 2.6408 xC_x/(log x)²` |
| `ChenTheorem/Main/KeyInequality.lean` | Complete proof of inequality (28): finite partition, two-witness injection, repeated-prime encoding of nonsquarefree exceptions, and the `O(x^0.9)` reciprocal-square tail |
| `ChenTheorem/Main/ShiftedEstimate.lean` | The isolated quantitative input for the fixed-shift version, pending a shifted copy of the sieve infrastructure |
| `ChenTheorem/Main.lean` | Completed deductions of inequality (28), Theorem 1 (`P_x(1,2) ≥ 0.67 xC_x/(log x)²` and Chen's theorem proper), and Theorem 2 (twin analogue) from the named upstream estimates |

## Correspondence with the paper

| Paper | Lean |
|---|---|
| `(1,2)`, `P₂` numbers | `Chen.IsP2` |
| `P_x(1,2)` | `Chen.chenCount` |
| `x_h(1,2)` | `Chen.chenCountShift` |
| `C_x` | `Chen.chenConst` (with `Chen.twinConst` the infinite product) |
| `Φ(y)` (Lemma 1) | `Chen.chenPhi` (defined via the incomplete-gamma formula derived inside Lemma 1, rather than the contour integral) |
| `f(k)`, `S`, `λ_d` | `Chen.fW`, `Chen.sieveNorm`, `Chen.sieveWeight` |
| `Ω` | `Chen.sieveOmega` |
| `M₁` | `Chen.mOne` |
| Lemma 1 | `chenPhi_eq_zero`, `chenPhi_monotoneOn`, `chenPhi_nonneg`, `chenPhi_le_one`, `chenPhi_ge` (**all five proved**) |
| Lemma 2, eqs. (2)–(3) | `large_sieve`, `large_sieve_dyadic` |
| Lemma 3 | `lFunction_fourth_moment_with_height_log` proves the corrected height-logarithmic form on `2 ≤ q ≤ Q`; the printed log-`Q`-only claim remains documented as `Lemma3FourthMoment` but is not asserted as a theorem |
| Lemma 4 | `primitive_char_sum_bound` (general squarefree `k`, **proved**); `primitive_char_sum_bound_prime` (prime case, **proved**) |
| Lemma 5 | `sieveOmega_le_mOne_add_mTwo` (**proved**) |
| Lemma 6 | `mTwo_le` (final deduction **proved** from the stronger `mTwo_le_log12`); equations (12)–(21) are all proved, and the corrected Lemma-3 height logarithm is carried through the Cauchy/Hölder/kernel estimates. The only remaining analytic input is the classical zero-free region `primitive_zero_free_region` |
| Lemmas 5–6 combined | `sieveOmega_le_mOne` (deduction **proved**; depends on the pending Lemma 6 input) |
| Lemma 7 | `mOne_le` |
| Equation (24) | `equation24_integral_bound` (**proved**, no `sorryAx`) |
| Lemma 8 | `sieveOmega_le` (constant/error deduction proved; only the prime-distribution/partial-summation input `chenPairs_kernel_le_integral` remains pending) |
| `P_x(x, x^{1/10})`, `P_x(x, p', x^{1/10})` | `Chen.sievedPrimeCount`, `Chen.sievedPrimeCountAt` |
| Equation (27) | `equation27_integral_bound` (**proved**, no `sorryAx`) |
| Lemma 9 | `sieved_lower_bound` (equation (27) and the final numerical deduction are proved; the pre-(27) Richert–Bombieri input `richert_weighted_sieve_estimate` remains pending) |
| Inequality (28) | `key_inequality` (**proved**) |
| Theorem 1 | `chenCount_lower` (quantitative), `chen_theorem` (qualitative), both deductions proved |
| Theorem 2 | `chenCountShift_lower`, `chen_twin` (final deduction proved; shifted quantitative sieve input pending) |

## Design notes / deliberate simplifications

* **`≪` constants.** Vinogradov `≪` statements are rendered as `∃ C > 0, …`;
  "for all sufficiently large even `x`" is rendered as
  `∀ᶠ x in atTop, Even x → …`.
* **`Φ` via a real integral — Lemma 1 fully proved.** The paper defines `Φ` by a
  vertical contour integral and *proves* (inside Lemma 1) that it equals a
  normalized incomplete gamma integral for `y ≥ 1`. We adopt the latter as the
  definition, turning the whole of Lemma 1 into a statement in real analysis,
  and all five of its parts are proved (no `sorry`):
  `n! · Φ(y) = ∫_{(0, a(y)]} e^{-t} t^n dt` with `a(y) = (log x)^{1.1} log y`,
  `n = ⌊log x⌋`, compared against the convergent Euler integral
  `n! = ∫_{(0,∞)} e^{-t} t^n dt` (`Real.Gamma_eq_integral` specialized to
  `s = n + 1`, via `Real.Gamma_nat_eq_factorial`).
  * *Vanishing on `[0,1]`, nonnegativity, `≤ 1`* (`chenPhi_eq_zero`,
    `chenPhi_nonneg`, `chenPhi_le_one`): `log x > 0` (as `x > 1`) forces
    `a(y) ≤ 0` on `[0,1]`, emptying the defining interval `Ioc 0 (a y)`;
    nonnegativity and the bound `≤ 1` follow by comparing that interval's
    integral against `Ioi 0` (`MeasureTheory.setIntegral_nonneg`,
    `MeasureTheory.setIntegral_mono_set`).
  * *Monotonicity* (`chenPhi_monotoneOn`): splits on `y ≤ 1` (constant `0`) vs.
    `y > 1` (genuine monotonicity of `log`, hence of `a(y)`, hence of the
    growing-interval integral).
  * *The quantitative tail bound* (`chenPhi_ge`, the hardest part): reduces
    `1 - Φ(y)` to `(n!)⁻¹ ∫_{(a(y),∞)} e^{-t}t^n dt` via
    `Ioc 0 a ∪ Ioi a = Ioi 0`; bounds this by `(n!)⁻¹ ∫_{(2n,∞)}` since
    `a(y) ≥ 2n` follows from the hypothesis on `y`; rescales
    `t = nx` (`MeasureTheory.integral_comp_mul_left_Ioi`) to reduce to
    `∫_{(2,∞)} e^{-nx}x^n dx`; bounds the integrand there by
    `e^{n(log2-1)}e^{-nx/2}` using the concavity tangent line
    `log t ≤ t - 1` of `Real.log_le_sub_one_of_pos` (applied at `t = x/2`, so
    `log x ≤ log 2 + x/2 - 1`, tight at `x = 2`) via
    `MeasureTheory.integral_mono_of_nonneg` (which needs only the *majorant*'s
    integrability, not the integrand's); and closes the loop with the
    elementary factorial bound `n^n ≤ n! · eⁿ`, obtained from Mathlib's
    Stirling inequality `Stirling.le_factorial_stirling` by discarding the
    `√(2πn) ≥ 1` factor. The final numeric inequality has enormous slack
    (`log x ≥ 10⁴` against a requirement of roughly `log x ≥ 5`), so a loose
    bound `log 2 < 0.7` (`Real.log_two_lt_d9`) suffices throughout.
* **Lemma 4, proved.** For a prime modulus `p`, every nontrivial
  character is automatically primitive: its conductor divides `p`
  (`DirichletCharacter.conductor_dvd_level`), hence is `1` or `p`, and conductor
  `1` forces the character trivial (`DirichletCharacter.eq_one_iff_conductor_eq_one`).
  So `∑*_{χ mod p} χ(m) = (∑_{all χ} χ(m)) - χ₀(m)`, and both terms are computed
  in closed form: the first via Mathlib's orthogonality relation
  `DirichletCharacter.sum_characters_eq` (`= φ(p)` if `m ≡ 1 mod p`, else `0`),
  the second via `MulChar.one_apply`/`MulChar.map_nonunit` (`= 1` if `(m,p)=1`,
  else `0`). A three-way case split on `(m mod p = 1)` and `(m,p) = 1` then
  matches the bound `≤ (m-1,p)` exactly (with equality in the "generic" case
  `p ∤ m(m-1)`). This is a genuinely different — and shorter — route than the
  paper's own prime-modulus proof (which builds primitive characters explicitly
  from a primitive root mod `p`). For coprime moduli `a,b`, the formalization
  constructs the CRT equivalence between characters mod `ab` and pairs of
  characters mod `a,b`, proves that conductors multiply, and hence that
  primitivity and primitive character sums factor. Strong induction over a
  squarefree odd `k` then reduces the general bound to the prime case. The
  omitted case `(m,k) ≠ 1` in the paper is handled explicitly: every character
  value is zero.
* **Lemma 2, proved.** A centered-interval Sobolev inequality is applied to a
  trigonometric polynomial; Parseval and Farey-fraction separation give the
  additive large sieve. A machine-checked Gauss-sum identity and finite
  character orthogonality then give (2), including `|τ(χ)|² = q`. Covering
  `(D,Q]` by disjoint blocks `(2ⁱD,2ⁱ⁺¹D]` gives (3), with the explicit
  universal constant `8 + 2π`.
* **Lemma 6 / `M₂`.** The finite character-sum form of `M₂` is defined and
  Lemma 5 retains it explicitly:
  `Ω ≤ (M₁+M₂)/(1-ε) + O(x (log x)^{-2.01})`.  The estimate
  `M₂ ≪ x (log x)^{-2.01}` is now fully reduced, by machine-checked proofs,
  to the documented classical zero-free region with companion `L'/L` bound
  (`primitive_zero_free_region`).  The corrected Lemma-3 fourth moment is now
  proved and instantiated in the pipeline.  In particular
  `lemma6_large_pair_block_estimate_of_deriv_fourth_moment` (equations
  (13)–(20)) does not depend on `sorryAx` — its `Lemma 3` dependence is
  explicit in the hypothesis — and the equation-(21) small-conductor estimate
  is proved from `primitive_zero_free_region` alone.
* **Primitive character sums.** `Chen.primSum` sums over primitive
  `DirichletCharacter ℂ q` via a `tsum`, avoiding `Fintype` instance juggling for
  the degenerate modulus `q = 0` that never occurs in the ranges used.
  `DirichletCharacter.LFunction` additionally requires a `[NeZero q]` instance
  (it is undefined at `q = 0`), which a bound summation variable can't supply on
  its own; `Chen.lFourthTerm` works around this with a `dif` that produces `0`
  at `q = 0` and manufactures the instance from `q ≠ 0` otherwise.
* **Bound-variable type ascriptions.** Several `Finset.filter` predicates mix a
  natural-number membership test with real-exponent conditions, e.g.
  `fun k => 1 ≤ k ∧ (k : ℝ) ≤ x ^ (1/4) ∧ k.Coprime x`. Left unannotated, Lean's
  elaborator can process the real-number ascription before the ambient type of
  `k` is unified with `ℕ` (postponed dot-notation resolution), silently
  defaulting the bound variable to `ℝ`. Every such lambda is annotated
  `fun k : ℕ => …` to force the type immediately.
* **Theorem 2's constant.** The singular series for `p + h` is `chenConst h`
  (product over odd primes dividing `h`), which is what the paper's `C_x` means
  in that context.
* Everything is stated for **natural-number subtraction** `x - p`, harmless since
  all statements only concern `p ≤ x`.
* **`chenPhi_ge` needed an extra `1 < x` hypothesis.** `Real.log` in Mathlib is
  defined via `|x|` for negative reals, so `Real.log x ≥ 10⁴` alone does not
  pin `x` down to a large *positive* number (e.g. `x = -e^{10⁴}` also satisfies
  it) — and unlike `chenPhi` itself (which only ever sees `x` through `log x`),
  `chenPhi_ge`'s conclusion involves genuine real exponentiation `x ^ (-0.1 : ℝ)`
  directly, which behaves differently at negative bases. The other four parts
  of Lemma 1 already carried a `1 < x` hypothesis for the same reason; this one
  had been missing it and has been corrected to match.

## Status

Builds cleanly with `lake build` (Lean `v4.32.1`, Mathlib `v4.32.1`) with zero
errors; the only warning is the intentional `declaration uses 'sorry'` for the
documented zero-free-region placeholder `primitive_zero_free_region`
(`Lemma6/ZeroFreeRegion.lean`).

**Lemma 1 is fully proved** — all five parts (`chenPhi_eq_zero`, `chenPhi_nonneg`,
`chenPhi_le_one`, `chenPhi_monotoneOn`, `chenPhi_ge`), no `sorry`, built on top of
seven supporting private lemmas (Gamma-integral/factorial identities, the
concavity tangent-line bound, the Stirling-derived factorial bound, and the
rescaling/tail estimates).

**Lemma 4 is fully proved** (`primitive_char_sum_bound`), using CRT
multiplicativity and strong induction, with the prime case
(`primitive_char_sum_bound_prime`) established via Dirichlet-character
orthogonality — see the design note above.

**Lemma 2 is fully proved** (`large_sieve`, `large_sieve_dyadic`) through the
three modules under `ChenTheorem/LargeSieve/`; neither theorem depends on
`sorryAx`.

**Lemma 5 is fully proved** (`sieveOmega_le_mOne_add_mTwo`).  Its
dimension-two upper-bound sieve is organized under `ChenTheorem/Lemma5/`;
in particular the large-base smoothing boundary is bounded by
`O(x (log x)^{-2.01})` using a short transition interval, optimal Selberg
weights, the lower bound `G(R) ≫ (log x)^1.97`, and the prime harmonic estimate.

The height-logarithmic `L`-function fourth moment supported by Chen's Lemma 3
calculation is proved in `Lemma3/FourthMoment.lean`.  The stronger printed
log-`Q`-only claim is not used.  The classical zero-free region
(`primitive_zero_free_region`, `Lemma6/ZeroFreeRegion.lean`) is the sole
remaining `sorry` input behind Lemma 6.  Everything else is machine-checked: the
finite Mellin reduction, the A/B decomposition, both large-conductor regimes
(19)–(20) (`lemma6_large_pair_block_estimate_of_deriv_fourth_moment` is
`sorryAx`-free), the full equation-(21) contour shift to
`Re s = 1 - 1/√(log x)` with its horizontal-edge and vertical-line estimates
(`Lemma6/Equation21.lean`, proved from `primitive_zero_free_region` alone),
the elementary prime-pair estimate after the shift, and the final exponent
deduction including `mTwo_le_log12 ⇒ mTwo_le`.  The prime-distribution
inputs behind Lemmas 7–9 and the shifted quantitative sieve estimate still
contain documented `sorry` placeholders. The paper-internal numerical
integrals (24) and (27) are complete and do not depend on `sorryAx`.
Inequality (28), including its exceptional `x^0.91` tail, is complete.
`Main.lean` itself has no
proof placeholders: the numerical deduction of Theorem 1, extraction of an
actual representation, and the infinitude argument for Theorem 2 are
machine-checked from those named interfaces.  Lemmas 1, 2, 4, and 5 are
complete machine-checked proofs.
