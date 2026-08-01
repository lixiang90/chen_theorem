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
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

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
noncomputable def sieveNormIndices (x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    (fun k : ℕ => 1 ≤ k ∧
      (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ∧ k.Coprime x)

/-- Indices in the numerator of `λ_d`. -/
noncomputable def sieveNumeratorIndices
    (x : ℕ) (ε : ℝ) (d : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    (fun k : ℕ => 1 ≤ k ∧
      (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) / d ∧
        k.Coprime (x * d))

/-- The numerator sum occurring in `λ_d`. -/
noncomputable def sieveNumerator (x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ sieveNumeratorIndices x ε d,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k

/-- The normalizing sum `S = ∑_{1 ≤ k ≤ x^{1/4 - ε/2}, (k,x) = 1} μ²(k)/f(k)`. -/
noncomputable def sieveNorm (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ sieveNormIndices x ε,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k

/-- Chen's sieve weights `λ_d`: `λ_1 = 1`, `λ_d = 0` for `d > x^{1/4 - ε/2}`, and
for `1 < d ≤ x^{1/4 - ε/2}`
`λ_d = (μ(d) φ(d) / f(d)) · (∑_{k ≤ x^{1/4-ε/2}/d, (k,xd)=1} μ²(k)/f(k)) / S`.
The paper shows `|λ_d| ≤ 1` for all `d`. -/
noncomputable def sieveWeight (x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then 1
  else if (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/4 - ε/2) then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Nat.totient d : ℝ) / fW d *
      (sieveNumerator x ε d / sieveNorm x ε)
  else 0

/-- The set of prime pairs `(p₁, p₂)` with
`x^{1/10} < p₁ ≤ x^{1/3} < p₂ ≤ (x/p₁)^{1/2}`, over which all main sums of the
paper range. -/
noncomputable def chenPairs (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (x + 1)) ×ˢ Finset.range (x + 1)).filter fun q =>
    q.1.Prime ∧ q.2.Prime ∧
      (x : ℝ) ^ ((1 : ℝ)/10) < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ)/3) ∧
      (x : ℝ) ^ ((1 : ℝ)/3) < (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ ((x : ℝ) / q.1) ^ ((1 : ℝ)/2)

/-- `chenRough x n` says that `n` has no prime divisor at most `x^(1/4)`.
This is the condition `(n, Q) = 1` in the paper, where
`Q = ∏_{2 ≤ p ≤ x^(1/4)} p`. -/
def chenRough (x n : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) → ¬r ∣ n

/-- The admissible third primes for a fixed pair `(p₁,p₂)` in `Ω`. -/
noncomputable def omegaThirdPrimes (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p₃ : ℕ =>
    p₃.Prime ∧ (p₃ : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) ∧
      chenRough x (x - q.1 * q.2 * p₃)

/-- The admissible von Mangoldt indices for a fixed pair `(p₁,p₂)` in `M`. -/
noncomputable def sieveMIndices (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n : ℕ =>
    (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) ∧
      chenRough x (x - q.1 * q.2 * n)

/-- Indices `n ≤ x/(p₁p₂)` in the smoothed sums of equations (5)–(7).
Unlike `sieveMIndices`, this set does not impose the roughness condition; that
condition has already been expanded using the square of the sieve weights. -/
noncomputable def smoothedMIndices (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n : ℕ =>
    (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2)

/-- The nonnegative smoothed summand common to `M₁`, `M₃`, and equation (6). -/
noncomputable def smoothedMKernel
    (x : ℕ) (q : ℕ × ℕ) (n : ℕ) : ℝ :=
  (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
    ArithmeticFunction.vonMangoldt n *
      chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))

/-- A flat finite index set for the smoothed `(p₁,p₂,n)` sums.  The product
representation is convenient when applying character orthogonality once to
the whole inner sum in equation (6). -/
noncomputable def smoothedMTriples (x : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (chenPairs x ×ˢ Finset.range (x + 1)).filter fun z =>
    z.2 ∈ smoothedMIndices x z.1

/-- The integer to which the residue-class condition in equation (6) is
applied. -/
def smoothedMArgument (z : (ℕ × ℕ) × ℕ) : ℕ :=
  z.1.1 * z.1.2 * z.2

/-- The part of the smoothed index set on which the principal character
modulo `d` is nonzero.  Its complement is precisely the finite `M₃`
remainder. -/
noncomputable def smoothedMGoodTriples (x d : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (smoothedMTriples x).filter fun z =>
    (smoothedMArgument z).Coprime d

/-- The complementary triples whose argument is not coprime to `d`. -/
noncomputable def smoothedMBadTriples (x d : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (smoothedMTriples x).filter fun z =>
    ¬(smoothedMArgument z).Coprime d

/-- Total smoothed mass on the coprime part of equation (6). -/
noncomputable def smoothedMGoodMass (x d : ℕ) : ℝ :=
  ∑ z ∈ smoothedMGoodTriples x d,
    smoothedMKernel x z.1 z.2

/-- Total smoothed mass lost when the principal character is extended from
the coprime triples to all triples. -/
noncomputable def smoothedMBadMass (x d : ℕ) : ℝ :=
  ∑ z ∈ smoothedMBadTriples x d,
    smoothedMKernel x z.1 z.2

/-- The admissible third primes below the threshold
`(x/(p₁p₂))^(1-ε)`. -/
noncomputable def omegaSmallThirdPrimes
    (x : ℕ) (ε : ℝ) (q : ℕ × ℕ) : Finset ℕ :=
  (omegaThirdPrimes x q).filter fun p₃ =>
    (p₃ : ℝ) < ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)

/-- The sifted count `Ω` of the paper: the number of triples `(p₁, p₂, p₃)` of primes
with `x^{1/10} < p₁ ≤ x^{1/3} < p₂ ≤ (x/p₁)^{1/2}`, `p₃ ≤ x/(p₁p₂)`, such that
`x - p₁p₂p₃` has no prime factor `≤ x^{1/4}` (i.e. `(x - p₁p₂p₃, Q) = 1` where
`Q = ∏_{2 ≤ p ≤ x^{1/4}} p`). -/
noncomputable def sieveOmega (x : ℕ) : ℕ :=
  ∑ q ∈ chenPairs x,
    (omegaThirdPrimes x q).card

/-- The weighted prime-power sum `M` preceding equation (5) of the paper:
`M = ∑_{(p₁,p₂)} log(x/(p₁p₂))⁻¹
       ∑_{n ≤ x/(p₁p₂), (x-p₁p₂n,Q)=1} Λ(n)`.

This is deliberately a finite sum.  The `n = 0` term is harmless since
`Λ(0) = 0`. -/
noncomputable def sieveM (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ sieveMIndices x q, ArithmeticFunction.vonMangoldt n

/-- The small-`p₃` remainder in the elementary reduction `Ω → M`.
It counts only triples already occurring in `Ω`, with the additional condition
`p₃ < (x/(p₁p₂))^(1-ε)`.  A later elementary estimate bounds this by a fixed
power saving. -/
noncomputable def sieveMSmallTail (x : ℕ) (ε : ℝ) : ℕ :=
  ∑ q ∈ chenPairs x,
    (omegaSmallThirdPrimes x ε q).card

/-- Integer majorant for the small-`p₃` tail, obtained by forgetting
primality and roughness and retaining only
`p₃ < (x/(p₁p₂))^(1-ε)`. -/
noncomputable def sieveMSmallMajorant (x : ℕ) (ε : ℝ) : ℕ :=
  ∑ q ∈ chenPairs x,
    ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊

/-- The coefficient obtained by collecting the pair of sieve weights
`λ_{d₁} λ_{d₂}` according to
`lcm(d₁,d₂) = d₁d₂/gcd(d₁,d₂) = d`.

For squarefree `d`, Lemma 5 bounds its absolute value by `3^ν(d)`. -/
noncomputable def sieveLcmCoeff (x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
      (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
    sieveWeight x ε q.1 * sieveWeight x ε q.2

/-- Number `ν(d)` of distinct prime divisors of `d`.  On the squarefree support
of Chen's sieve weights this is the number denoted by `ν(d)` in the paper. -/
def distinctPrimeFactors (d : ℕ) : ℕ := d.primeFactors.card

/-- Finite sum of `F` over the nontrivial Dirichlet characters modulo `d`.
The `d = 0` branch is set to zero; every occurrence below has `1 ≤ d`. -/
noncomputable def nontrivialCharSum (d : ℕ)
    (F : DirichletCharacter ℂ d → ℂ) : ℂ :=
  if h : d = 0 then 0
  else
    have : NeZero d := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ d, if χ = 1 then 0 else F χ

/-- Moduli on the square-sieve support after collecting
`lcm(d₁,d₂)=d`. -/
noncomputable def sieveModuli (x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d : ℕ =>
    1 ≤ d ∧ d.Coprime x ∧
      (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε)

/-- The main sieve sum `M₁`, after collecting the pair of sieve weights by
`lcm(d₁,d₂)`.  This is the finite form used after equation (6); expanding
`sieveLcmCoeff` recovers the double sum in the paper. -/
noncomputable def mOne (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    sieveLcmCoeff x ε d / (Nat.totient d : ℝ) *
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n

/-- The smoothed square-sieve expansion on the left of equation (6), already
collected by the lcm modulus. -/
noncomputable def smoothedSieveExpansion (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    sieveLcmCoeff x ε d *
      ∑ z ∈ smoothedMTriples x,
        smoothedMKernel x z.1 z.2 *
          (if x ≡ smoothedMArgument z [MOD d] then 1 else 0)

/-- The signed bad-coprimality remainder `M₃` in equations (7)–(8), after
collecting the two sieve weights according to their lcm. -/
noncomputable def mThree (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    sieveLcmCoeff x ε d / (Nat.totient d : ℝ) *
      smoothedMBadMass x d

/-- Positive coefficient majorant for `|M₃|`. -/
noncomputable def mThreeMajorant (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      |smoothedMBadMass x d|

/-- Nonprincipal character contribution before replacing a character modulo
`d` by its primitive associate.  This is the finite von Mangoldt form of
`M₄`'s inner character sum. -/
noncomputable def imprimitiveCharacterContribution (x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ (x : ZMod d)) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod d))

/-- Signed real part of the nonprincipal contribution in equation (6). -/
noncomputable def mFourSigned (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    sieveLcmCoeff x ε d / (Nat.totient d : ℝ) *
      (imprimitiveCharacterContribution x d).re

/-- The same finite contribution after every character is replaced by the
primitive character of its conductor. -/
noncomputable def primitiveCharacterContribution (x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ.primitiveCharacter x) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ.primitiveCharacter (q.1 * q.2 * n))

/-- Primitive-character mass on the indices where the original character
modulo `d` vanishes.  This is the finite prime-power form of the Euler-factor
correction in `M₅`. -/
noncomputable def primitiveBadCharacterContribution (x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ.primitiveCharacter x) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
          (smoothedMKernel x q n : ℂ) *
            χ.primitiveCharacter (q.1 * q.2 * n))

/-- Positive majorant `M₄` for the imprimitive nonprincipal contribution,
after collecting the sieve weights by their lcm. -/
noncomputable def mFour (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖imprimitiveCharacterContribution x d‖

/-- The finite imprimitive-to-primitive discrepancy `M₅`. -/
noncomputable def mFive (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖imprimitiveCharacterContribution x d -
          primitiveCharacterContribution x d‖

/-- Finite-sum form of the primitive-character error `M₂`.

The paper writes this quantity as a vertical integral involving `L'/L`. For
Lemma 5 it is more convenient to use the equivalent finite von Mangoldt sum
displayed below. `Lemma6/Core.lean` introduces the conductor-grouped finite
counterpart `lemma6Nm`; proving the Mellin/contour identification is part of
the isolated equation-(12) target.

For each character modulo `d`, `χ.primitiveCharacter` is the primitive
character of conductor `d*` inducing `χ`. -/
noncomputable def mTwo (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖primitiveCharacterContribution x d‖

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
