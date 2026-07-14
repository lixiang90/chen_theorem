# Formal skeleton of Chen's theorem (1 + 2) in Lean 4 / Mathlib

This is a Lake project giving a **formal skeleton** — precise Lean statements with
`sorry` proofs — of Chen Jingrun's 1973 paper

> Chen Jingrun, *On the representation of a large even integer as the sum of a
> prime and the product of at most two primes*, Sci. Sinica **16** (1973), 111–128.

(A LaTeX transcription of the paper, in Chinese and English, lives in the parent
directory: `../latex/main.tex`, `../latex/main_en.tex`.)

- **Lean**: `leanprover/lean4:v4.31.0`
- **Mathlib**: release tag `v4.31.0`

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
| `ChenTheorem/SieveLemmas.lean` | Lemmas 1–4: properties of `Φ`, the large sieve, the `L`-function fourth moment, primitive character sums |
| `ChenTheorem/MainEstimates.lean` | Lemmas 5–9: the sieve decomposition, `M₁ ≤ …`, `Ω ≤ 3.9404 xC_x/(log x)²`, the Richert-sieve lower bound `≥ 2.6408 xC_x/(log x)²` |
| `ChenTheorem/Main.lean` | Inequality (28), Theorem 1 (`P_x(1,2) ≥ 0.67 xC_x/(log x)²` and Chen's theorem proper), Theorem 2 (twin analogue) |

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
| Lemma 3 | `lFunction_fourth_moment` |
| Lemma 4 | `primitive_char_sum_bound` (general squarefree `k`, open); `primitive_char_sum_bound_prime` (prime case, **proved**) |
| Lemmas 5–6 | `sieveOmega_le_mOne` (combined; `M₂` and its contour integral are not reproduced — only the resulting bound) |
| Lemma 7 | `mOne_le` |
| Lemma 8 | `sieveOmega_le` |
| `P_x(x, x^{1/10})`, `P_x(x, p', x^{1/10})` | `Chen.sievedPrimeCount`, `Chen.sievedPrimeCountAt` |
| Lemma 9 | `sieved_lower_bound` |
| Inequality (28) | `key_inequality` |
| Theorem 1 | `chenCount_lower` (quantitative), `chen_theorem` (qualitative) |
| Theorem 2 | `chenCountShift_lower`, `chen_twin` |

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
* **Lemma 4, prime case, proved.** For a prime modulus `p`, every nontrivial
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
  paper's own proof (which builds primitive characters explicitly from a
  primitive root mod `p`); it does not generalize past the prime case, since for
  composite squarefree `k` not every nontrivial character mod `k` is primitive
  (that direction needs the CRT decomposition into characters mod each prime
  factor, which `primitive_char_sum_bound` for general `k` still requires and
  does not yet have).
* **`M₂` omitted.** The quantity `M₂` (a contour integral of `L'/L` against the
  sieve weights) is not defined; Lemmas 5 and 6 are stated in combined form
  `Ω ≤ M₁/(1-ε) + O(x (log x)^{-2.01})`, which is exactly how the pair is used.
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

Builds cleanly with `lake build` (Lean `v4.31.0`, Mathlib `v4.31.0`): all
definitions and all 21 theorem statements elaborate with zero errors.

**Lemma 1 is fully proved** — all five parts (`chenPhi_eq_zero`, `chenPhi_nonneg`,
`chenPhi_le_one`, `chenPhi_monotoneOn`, `chenPhi_ge`), no `sorry`, built on top of
seven supporting private lemmas (Gamma-integral/factorial identities, the
concavity tangent-line bound, the Stirling-derived factorial bound, and the
rescaling/tail estimates).

**Lemma 4's prime case is proved** (`primitive_char_sum_bound_prime`), via
Dirichlet-character orthogonality rather than the paper's primitive-root
construction — see the design note above.

The large sieve, the `L`-function fourth moment, the general (squarefree)
case of Lemma 4, and everything in `MainEstimates.lean`/`Main.lean` remain
`sorry`-placeholders. This is still a *skeleton* overall, but two of the
paper's foundational tools — Lemma 1 in full, and the base case of Lemma 4 —
are now complete, machine-checked proofs.
