import ChenTheorem.Defs
import Mathlib.Data.Nat.Dist

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-!
# Fixed-shift sieve objects for Theorem 2

For Theorem 1 the scale and the residue being sieved are both the even number
`x`: the candidate prime is `x - p₁p₂n`.  For Theorem 2 the scale is still
`x`, but the residue is the fixed even shift `h`: the candidate prime is
`p₁p₂n - h`.  Keeping these two parameters separate is the essential change
behind the parallel versions of Lemmas 5--9.

All product ranges below are cut off at `x`.  Consequently they count the
subset `p + h ≤ x` of `chenCountShift h x`; this is enough for the eventual
lower bound and avoids an artificial `x + h` endpoint throughout the sieve.
-/

/-- A positive integer `n - h` with no prime divisor at most `x^(1/4)`.
The strict inequality excludes the truncated-subtraction value zero. -/
def shiftedRough (h x n : ℕ) : Prop :=
  h < n ∧ chenRough x (n - h)

/-- Normalizing indices for the shifted Selberg weights.  The size cutoff is
controlled by `x`, while coprimality is with the fixed residue `h`. -/
noncomputable def shiftedSieveNormIndices
    (h x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    (fun k : ℕ => 1 ≤ k ∧
      (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ∧ k.Coprime h)

/-- Numerator indices for the shifted Selberg weights. -/
noncomputable def shiftedSieveNumeratorIndices
    (h x : ℕ) (ε : ℝ) (d : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    (fun k : ℕ => 1 ≤ k ∧
      (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) / d ∧
        k.Coprime (h * d))

noncomputable def shiftedSieveNumerator
    (h x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ shiftedSieveNumeratorIndices h x ε d,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k

noncomputable def shiftedSieveNorm (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ shiftedSieveNormIndices h x ε,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k

/-- Chen's Selberg weight with fixed residue `h` and independent scale `x`. -/
noncomputable def shiftedSieveWeight
    (h x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then 1
  else if (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Nat.totient d : ℝ) / fW d *
      (shiftedSieveNumerator h x ε d / shiftedSieveNorm h x ε)
  else 0

def shiftedSieveDivisorUniverse (h x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d => 1 ≤ d ∧ d.Coprime h

noncomputable def shiftedSieveDivisorSum
    (h x : ℕ) (ε : ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ (shiftedSieveDivisorUniverse h x).filter (fun d => d ∣ a),
    shiftedSieveWeight h x ε d

/-- Third primes in the shifted exceptional triple sum. -/
noncomputable def shiftedOmegaThirdPrimes
    (h x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p₃ : ℕ =>
    p₃.Prime ∧ (p₃ : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) ∧
      shiftedRough h x (q.1 * q.2 * p₃)

/-- Shifted `Ω`: products `p₁p₂p₃ ≤ x` for which
`p₁p₂p₃ - h` has no small prime divisor. -/
noncomputable def shiftedSieveOmega (h x : ℕ) : ℕ :=
  ∑ q ∈ chenPairs x, (shiftedOmegaThirdPrimes h x q).card

/-- Von Mangoldt indices in the shifted analogue of the sum `M`. -/
noncomputable def shiftedSieveMIndices
    (h x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n : ℕ =>
    (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) ∧
      shiftedRough h x (q.1 * q.2 * n)

/-- The shifted weighted prime-power sum preceding equation (5). -/
noncomputable def shiftedSieveM (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ shiftedSieveMIndices h x q,
        ArithmeticFunction.vonMangoldt n

noncomputable def shiftedSmoothedRoughM (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ shiftedSieveMIndices h x q, smoothedMKernel x q n

/-- The exact loss caused by inserting `chenPhi` into the fixed-shift
von-Mangoldt sum. -/
noncomputable def shiftedSieveMSmoothingError (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ shiftedSieveMIndices h x q,
        ArithmeticFunction.vonMangoldt n *
          (1 - chenPhi x
            ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)))

/-- The thin transition interval on which Lemma 1 does not yet give the
uniform `x⁻⁰·¹` smoothing loss. -/
noncomputable def shiftedSmoothingBoundaryIndices
    (h x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (shiftedSieveMIndices h x q).filter fun n =>
    (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))

noncomputable def shiftedSmoothingBoundaryMass (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ shiftedSmoothingBoundaryIndices h x q,
        ArithmeticFunction.vonMangoldt n

noncomputable def shiftedSmoothingBoundarySmallBaseMass
    (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter fun n =>
          (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

noncomputable def shiftedSmoothingBoundaryLargeBaseMass
    (h x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter fun n =>
          ¬(n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

noncomputable def shiftedOmegaSmallThirdPrimes
    (h x : ℕ) (ε : ℝ) (q : ℕ × ℕ) : Finset ℕ :=
  (shiftedOmegaThirdPrimes h x q).filter fun p₃ =>
    (p₃ : ℝ) < ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)

noncomputable def shiftedSieveMSmallTail
    (h x : ℕ) (ε : ℝ) : ℕ :=
  ∑ q ∈ chenPairs x, (shiftedOmegaSmallThirdPrimes h x ε q).card

/-- The same shift-independent majorant used for the small-third-prime tail. -/
noncomputable def shiftedSieveMSmallMajorant (x : ℕ) (ε : ℝ) : ℕ :=
  ∑ q ∈ chenPairs x,
    ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊

noncomputable def shiftedSieveLcmCoeff
    (h x : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
      (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
    shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2

noncomputable def shiftedSieveModuli
    (h x : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d : ℕ =>
    1 ≤ d ∧ d.Coprime h ∧
      (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε)

/-- Principal-character term in the shifted sieve expansion. -/
noncomputable def shiftedMOne (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ) *
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n

/-- Shifted square-sieve expansion: the residue condition is now
`h ≡ p₁p₂n (mod d)`. -/
noncomputable def shiftedSmoothedSieveExpansion
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    shiftedSieveLcmCoeff h x ε d *
      ∑ z ∈ smoothedMTriples x,
        smoothedMKernel x z.1 z.2 *
          (if h ≡ smoothedMArgument z [MOD d] then 1 else 0)

noncomputable def shiftedSquareSieveExpansion
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ smoothedMIndices x q,
      smoothedMKernel x q n *
        (shiftedSieveDivisorSum h x ε (Nat.dist h (q.1 * q.2 * n))) ^ 2

noncomputable def shiftedMThree (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ) *
      smoothedMBadMass x d

noncomputable def shiftedMThreeMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      |smoothedMBadMass x d|

noncomputable def shiftedImprimitiveCharacterContribution
    (h x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ (h : ZMod d)) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod d))

noncomputable def shiftedMFourSigned (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ) *
      (shiftedImprimitiveCharacterContribution h x d).re

noncomputable def shiftedPrimitiveCharacterContribution
    (h x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ.primitiveCharacter h) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ.primitiveCharacter (q.1 * q.2 * n))

noncomputable def shiftedPrimitiveBadCharacterContribution
    (h x d : ℕ) : ℂ :=
  nontrivialCharSum d (fun χ =>
    starRingEnd ℂ (χ.primitiveCharacter h) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
          (smoothedMKernel x q n : ℂ) *
            χ.primitiveCharacter (q.1 * q.2 * n))

noncomputable def shiftedMFour (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖shiftedImprimitiveCharacterContribution h x d‖

noncomputable def shiftedMFive (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖shiftedImprimitiveCharacterContribution h x d -
          shiftedPrimitiveCharacterContribution h x d‖

/-- Primitive-character error term in the shifted analogue of Lemma 6. -/
noncomputable def shiftedMTwo (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
      ‖shiftedPrimitiveCharacterContribution h x d‖

/-- Primes `p ≤ x` for which `p+h` has no odd prime divisor at most
`x^(1/10)`. -/
noncomputable def shiftedSievedPrimeCount (h x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) → ¬r ∣ (p + h)).card

/-- The shifted correction count with the additional divisor `p' ∣ p+h`. -/
noncomputable def shiftedSievedPrimeCountAt
    (h x p' : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ p' ∣ (p + h) ∧
      ∀ r : ℕ, r.Prime → 2 < r →
        (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) → ¬r ∣ (p + h)).card

/-- The product-bounded shifted Chen count used by the sieve. -/
noncomputable def shiftedChenCountCore (h x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ IsP2 (p + h) ∧ p + h ≤ x).card

end Chen
