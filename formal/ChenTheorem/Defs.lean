/-
Formal skeleton of Chen Jingrun's theorem "(1,2)", following:

  Chen Jingrun, *On the representation of a large even integer as the sum of
  a prime and the product of at most two primes*, Sci. Sinica 16 (1973), 111–128.

This file defines the main objects of the paper:

* `Chen.IsP2`               : "prime or product of two primes" (a `P₂` number)
* `Chen.chenCount`          : the counting function `P_x(1,2)`
* `Chen.chenCountShift`     : the counting function `x_h(1,2)` (twin analogue)
* `Chen.twinConst`          : the twin-prime constant `∏_{p>2} (1 - (p-1)⁻²)`
* `Chen.chenConst`          : the singular series `C_x`
* `Chen.chenPhi`            : the smoothing function `Φ` of Lemma 1
* `Chen.fW`, `Chen.sieveNorm`, `Chen.sieveWeight` : the sieve weights `f`, `S`, `λ_d`
* `Chen.chenPairs`          : the prime pairs `x^{1/10} < p₁ ≤ x^{1/3} < p₂ ≤ (x/p₁)^{1/2}`
* `Chen.sieveOmega`         : the sifted triple count `Ω`
* `Chen.mOne`               : the main sieve sum `M₁`
* `Chen.sievedPrimeCount`, `Chen.sievedPrimeCountAt`, `Chen.midPrimes` :
  the quantities `P_x(x, x^{1/10})`, `P_x(x, p', x^{1/10})` of Lemma 9

All definitions are stated for the current Mathlib. Real-exponent conditions
(`p ≤ x^{1/3}` and the like) make most predicates undecidable, so definitions are
`noncomputable` and use classical decidability.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Filter Real
open scoped Classical

namespace Chen

/-- `IsP2 n` : `n` is a prime, or a product of two primes (a "`P₂`" number).
In the paper this is the condition `x - p = p₁` or `x - p = p₂p₃`. -/
def IsP2 (n : ℕ) : Prop :=
  n.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

/-- `P_x(1,2)` : the number of primes `p ≤ x` such that `x - p` is a prime
or a product of two primes. -/
noncomputable def chenCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p => p.Prime ∧ IsP2 (x - p)).card

/-- `x_h(1,2)` : the number of primes `p ≤ x` such that `p + h` is a prime
or a product of two primes. -/
noncomputable def chenCountShift (h x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p => p.Prime ∧ IsP2 (p + h)).card

/-- The twin-prime constant `∏_{p > 2} (1 - 1/(p-1)²)`. -/
noncomputable def twinConst : ℝ :=
  ∏' p : Nat.Primes, if 2 < (p : ℕ) then 1 - (1 : ℝ) / ((p : ℕ) - 1) ^ 2 else 1

/-- The singular series
`C_x = ∏_{p ∣ x, p > 2} (p-1)/(p-2) · ∏_{p > 2} (1 - 1/(p-1)²)`. -/
noncomputable def chenConst (x : ℕ) : ℝ :=
  (∏ p ∈ x.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) * twinConst

/-- Chen's smoothing function `Φ` (Lemma 1). The paper defines `Φ(y)` as a vertical
contour integral
`Φ(y) = (2πi)⁻¹ ∫_{(2)} y^ω ω⁻¹ (1 + ω/(log x)^{1.1})^{-[log x]-1} dω`;
the computation inside Lemma 1 shows that for `y ≥ 1` it equals the normalized
incomplete-gamma integral below, which we take as the *definition* here (for
`0 ≤ y ≤ 1` both sides vanish, since the integration interval is empty). -/
noncomputable def chenPhi (x y : ℝ) : ℝ :=
  ((⌊Real.log x⌋₊.factorial : ℝ))⁻¹ *
    ∫ t in Set.Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y),
      Real.exp (-t) * t ^ ⌊Real.log x⌋₊

/-- The multiplicative weight `f(k) = φ(k) ∏_{p ∣ k} (p-2)/(p-1)` used in the
definition of the sieve weights `λ_d`. (`f(k) = 0` for even `k`; all `k`
appearing in the sums below are coprime to the even number `x`.) -/
noncomputable def fW (k : ℕ) : ℝ :=
  (Nat.totient k : ℝ) * ∏ p ∈ k.primeFactors, ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- The normalizing sum `S = ∑_{1 ≤ k ≤ x^{1/4 - ε/2}, (k,x) = 1} μ²(k)/f(k)`. -/
noncomputable def sieveNorm (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (x + 1)).filter
      (fun k : ℕ => 1 ≤ k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/4 - ε/2) ∧ k.Coprime x),
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k

/-- Chen's sieve weights `λ_d`: `λ_1 = 1`, `λ_d = 0` for `d > x^{1/4 - ε/2}`, and
for `1 < d ≤ x^{1/4 - ε/2}`
`λ_d = (μ(d) φ(d) / f(d)) · (∑_{k ≤ x^{1/4-ε/2}/d, (k,xd)=1} μ²(k)/f(k)) / S`.
The paper shows `|λ_d| ≤ 1` for all `d`. -/
noncomputable def sieveWeight (x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then 1
  else if (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/4 - ε/2) then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Nat.totient d : ℝ) / fW d *
      ((∑ k ∈ (Finset.range (x + 1)).filter
          (fun k : ℕ => 1 ≤ k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/4 - ε/2) / d ∧
            k.Coprime (x * d)),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) / sieveNorm x ε)
  else 0

/-- The set of prime pairs `(p₁, p₂)` with
`x^{1/10} < p₁ ≤ x^{1/3} < p₂ ≤ (x/p₁)^{1/2}`, over which all main sums of the
paper range. -/
noncomputable def chenPairs (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (x + 1)) ×ˢ Finset.range (x + 1)).filter fun q =>
    q.1.Prime ∧ q.2.Prime ∧
      (x : ℝ) ^ ((1 : ℝ)/10) < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/3) ∧
      (x : ℝ) ^ ((1 : ℝ)/3) < (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ ((x : ℝ) / q.1) ^ ((1 : ℝ)/2)

/-- The sifted count `Ω` of the paper: the number of triples `(p₁, p₂, p₃)` of primes
with `x^{1/10} < p₁ ≤ x^{1/3} < p₂ ≤ (x/p₁)^{1/2}`, `p₃ ≤ x/(p₁p₂)`, such that
`x - p₁p₂p₃` has no prime factor `≤ x^{1/4}` (i.e. `(x - p₁p₂p₃, Q) = 1` where
`Q = ∏_{2 ≤ p ≤ x^{1/4}} p`). -/
noncomputable def sieveOmega (x : ℕ) : ℕ :=
  ∑ q ∈ chenPairs x,
    ((Finset.range (x + 1)).filter fun p₃ : ℕ =>
      p₃.Prime ∧ (p₃ : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) ∧
        ∀ r : ℕ, r.Prime → (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/4) →
          ¬ r ∣ (x - q.1 * q.2 * p₃)).card

/-- The main sieve sum `M₁` of the paper (introduced after Lemma 4, estimated in
Lemma 7):
`M₁ = ∑_{(d₁,x)=1} ∑_{(d₂,x)=1} λ_{d₁} λ_{d₂} / φ(d₁d₂/(d₁,d₂)) ·
  ∑_{(p₁,p₂)} (log (x/p₁p₂))⁻¹ ∑_{n ≤ x/(p₁p₂)} Λ(n) Φ(x/(p₁p₂n))`. -/
noncomputable def mOne (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d₁ ∈ (Finset.range (x + 1)).filter (fun d => d.Coprime x),
    ∑ d₂ ∈ (Finset.range (x + 1)).filter (fun d => d.Coprime x),
      sieveWeight x ε d₁ * sieveWeight x ε d₂ /
          (Nat.totient (d₁ * d₂ / d₁.gcd d₂) : ℝ) *
        ∑ q ∈ chenPairs x,
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
            ∑ n ∈ (Finset.range (x + 1)).filter
                (fun n : ℕ => (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2)),
              ArithmeticFunction.vonMangoldt n *
                chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))

/-- `P_x(x, x^{1/10})` : the number of primes `p ≤ x` with `p ≢ x (mod r)` for every
odd prime `r ≤ x^{1/10}` (for `p ≤ x` this is the condition `r ∤ x - p`). -/
noncomputable def sievedPrimeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r → (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/10) →
      ¬ r ∣ (x - p)).card

/-- `P_x(x, p', x^{1/10})` : the number of primes `p ≤ x` with `p ≡ x (mod p')` and
`p ≢ x (mod r)` for every odd prime `r ≤ x^{1/10}`. -/
noncomputable def sievedPrimeCountAt (x p' : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ p' ∣ (x - p) ∧
      ∀ r : ℕ, r.Prime → 2 < r → (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/10) →
        ¬ r ∣ (x - p)).card

/-- The primes `p'` with `x^{1/10} < p' ≤ x^{1/3}`, over which the correction term
of Lemma 9 is summed. -/
noncomputable def midPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ (x : ℝ) ^ ((1 : ℝ)/10) < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/3)

end Chen
