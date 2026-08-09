/-
The prime-pair Dirichlet polynomial and the `A`, `B` summands introduced
between equations (16) and (17) in Chen's proof of Lemma 6.

The set of prime pairs is kept as an explicit finite parameter here.  In
`Core.lean` it is instantiated by one admissible `(k,m)` block.
-/
import ChenTheorem.Lemma6.LogDerivBound
import ChenTheorem.Lemma6.Dyadic
import ChenTheorem.SieveLemmas

open Real
open scoped Classical

namespace Chen

/-- Prime pairs surviving the cofactor coprimality condition in `N_m`. -/
noncomputable def lemma6AdmissiblePairs (x m : ℕ) : Finset (ℕ × ℕ) :=
  (chenPairs x).filter (fun q => Nat.Coprime (q.1 * q.2) m)

/-- The finite set of pair-product dyadic indices occupied for a fixed
cofactor. -/
noncomputable def lemma6PairBlockIndices (x m : ℕ) : Finset ℕ :=
  (lemma6AdmissiblePairs x m).image (lemma6PairBlockIndex x)

/-- The actual admissible `(k,m)` prime-pair block from equation (13). -/
noncomputable def lemma6AdmissiblePairBlock
    (x m k : ℕ) : Finset (ℕ × ℕ) :=
  (lemma6AdmissiblePairs x m).filter
    (fun q => q ∈ lemma6PairBlock x k)

/-- The prime-pair Dirichlet polynomial occurring in `A(l,k,s,m,H)` and
`B(l,k,s,m,H)`. -/
noncomputable def lemma6PairDirichletPolynomial
    {d : ℕ} (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ)
    (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ q ∈ pairs,
    χ (q.1 * q.2 : ZMod d) /
      (((q.1 * q.2 : ℕ) : ℂ) ^ s *
        (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))

/-- The prime-pair polynomial specialized to the actual `(k,m)` block. -/
noncomputable def lemma6PairBlockPolynomial
    {d : ℕ} (x m k : ℕ) (s : ℂ)
    (χ : DirichletCharacter ℂ d) : ℂ :=
  lemma6PairDirichletPolynomial x
    (lemma6AdmissiblePairBlock x m k) s χ

/-- The one-modulus `A` summand after equation (16). -/
noncomputable def lemma6AModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖)

/-- The raw first summand obtained directly from equation (16), before
using the standard bound for `L'/L` on `Re s > 1`.  Chen absorbs that bound
into the factor `x (log x)^2` preceding the printed `A` integral. -/
noncomputable def lemma6RawAModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ *
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖)

/-- The one-modulus `B` summand after equation (16). -/
noncomputable def lemma6BModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖deriv (DirichletCharacter.LFunction χ) s‖ *
      ‖lemma6MollifierAt H s χ‖)

/-- Summing the pointwise equation-(16) norm split over primitive
characters gives the raw `A + B` decomposition preceding (17). -/
theorem lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  simp only [lemma6RawAModulus, lemma6BModulus, primSum, tsum_fintype]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ.IsPrimitive
  · simp only [hχ, if_true]
    exact lemma6_pair_mul_logDeriv_norm_le_A_add_B (H := H) hx ν χ
      (lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ)
  · simp only [hχ, if_false]
    norm_num

/-- The explicit interface for the standard `L'/L` bound that Chen absorbs
into the factor `(log x)^2` in (17).  Once a uniform bound `C` is supplied,
the raw first summand is at most `C` times the printed `A` summand. -/
theorem lemma6RawAModulus_le_mul_AModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) {C : ℝ}
    (hlogDeriv : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤ C) :
    lemma6RawAModulus (d := d) x H pairs s ≤
      C * lemma6AModulus (d := d) x H pairs s := by
  simp only [lemma6RawAModulus, lemma6AModulus, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ.IsPrimitive
  · simp only [hχ, if_true]
    calc
      ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ *
          ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ ≤
        ‖lemma6PairDirichletPolynomial x pairs s χ‖ * C *
          ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ := by
          gcongr
          exact hlogDeriv χ hχ
      _ = C *
          (‖lemma6PairDirichletPolynomial x pairs s χ‖ *
            ‖1 - DirichletCharacter.LFunction χ s *
              lemma6MollifierAt H s χ‖) := by ring
  · simp only [hχ, if_false, mul_zero]
    exact le_rfl

/-- On Chen's `α`-line, the raw `A` summand is controlled by the universal
von Mangoldt majorant times the printed `A` summand. -/
theorem lemma6RawAModulus_le_majorant_mul_AModulus_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) ≤
      lemma6LogDerivMajorant (lemma6AlphaPoint x ν) *
        lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  apply lemma6RawAModulus_le_mul_AModulus
  intro χ hχ
  exact lemma6_norm_logDeriv_le_majorant χ
    (one_lt_lemma6AlphaPoint_re hx ν)

/-- Equation (16) followed by the standard majorization step that produces
the two printed integrands `A` and `B` in equation (17). -/
theorem lemma6_primitive_logDeriv_sum_le_majorant_mul_A_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      lemma6LogDerivMajorant (lemma6AlphaPoint x ν) *
          lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  have hsplit :=
    lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
      (d := d) (H := H) hx pairs ν
  have hraw :=
    lemma6RawAModulus_le_majorant_mul_AModulus_at_alpha
      (d := d) (H := H) hx pairs ν
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The raw `A` summand with Chen's explicit `(log x)^2` loss. -/
theorem lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
        lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  apply lemma6RawAModulus_le_mul_AModulus
  intro χ hχ
  exact (lemma6_norm_logDeriv_le_majorant χ
    (one_lt_lemma6AlphaPoint_re hx ν)).trans
      (lemma6LogDerivMajorant_alpha_le hx ν)

/-- The complete one-modulus equation-(16) estimate in the normalization
used in equation (17): `4 (log x)^2 A + B`. -/
theorem lemma6_primitive_logDeriv_sum_le_four_log_sq_mul_A_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  have hsplit :=
    lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
      (d := d) (H := H) hx pairs ν
  have hraw :=
    lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
      (d := d) (H := H) hx pairs ν
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The equation-(17) one-modulus estimate for the project's actual
admissible `(k,m)` prime-pair block. -/
theorem lemma6_pairBlock_logDeriv_sum_le_four_log_sq_mul_A_add_B
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (m k : ℕ) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k) (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H
          (lemma6AdmissiblePairBlock x m k) (lemma6AlphaPoint x ν) := by
  simpa only [lemma6PairBlockPolynomial] using
    lemma6_primitive_logDeriv_sum_le_four_log_sq_mul_A_add_B_at_alpha
      (d := d) (H := H) hx (lemma6AdmissiblePairBlock x m k) ν

/-- The printed `A` summand, totalized at modulus zero so it can be summed
over an unrestricted finite set of natural moduli. -/
noncomputable def lemma6AModulusTotal
    (d x m k H : ℕ) (s : ℂ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    lemma6AModulus (d := d) x H
      (lemma6AdmissiblePairBlock x m k) s

/-- The `B` summand, totalized at modulus zero. -/
noncomputable def lemma6BModulusTotal
    (d x m k H : ℕ) (s : ℂ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    lemma6BModulus (d := d) x H
      (lemma6AdmissiblePairBlock x m k) s

/-- The unsplit logarithmic-derivative summand on the `α`-line,
totalized at modulus zero. -/
noncomputable def lemma6LogDerivModulusAtAlpha
    (d x m k : ℕ) (ν : ℝ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    primSum d (fun χ =>
      ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
        (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖)

theorem lemma6LogDerivModulusAtAlpha_le
    (d : ℕ) {x H : ℕ} (hx : 2 ≤ x) (m k : ℕ) (ν : ℝ) :
    lemma6LogDerivModulusAtAlpha d x m k ν ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) +
        lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
  by_cases hd : d = 0
  · simp [lemma6LogDerivModulusAtAlpha, lemma6AModulusTotal,
      lemma6BModulusTotal, hd]
  · letI : NeZero d := ⟨hd⟩
    simp only [lemma6LogDerivModulusAtAlpha, lemma6AModulusTotal,
      lemma6BModulusTotal, dif_neg hd]
    exact lemma6_pairBlock_logDeriv_sum_le_four_log_sq_mul_A_add_B
      (d := d) (H := H) hx m k ν

/-- The equation-(17) `A` sum over one dyadic modulus block. -/
noncomputable def lemma6ABlockAtAlpha
    (x m l k H : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d *
      lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)

/-- The equation-(17) `B` sum on the original `α`-line over one dyadic
modulus block.  Moving this term to `β` is the next contour step. -/
noncomputable def lemma6BBlockAtAlpha
    (x m l k H : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d *
      lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)

/-- The unsplit logarithmic-derivative sum over one dyadic modulus block. -/
noncomputable def lemma6LogDerivBlockAtAlpha
    (x m l k : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d * lemma6LogDerivModulusAtAlpha d x m k ν

/-- Blockwise form of equation (16), in the normalization used at the
start of equation (17). -/
theorem lemma6LogDerivBlockAtAlpha_le
    {x H : ℕ} (hx : 2 ≤ x) (m l k : ℕ) (ν : ℝ) :
    lemma6LogDerivBlockAtAlpha x m l k ν ≤
      (4 * Real.log (x : ℝ) ^ 2) * lemma6ABlockAtAlpha x m l k H ν +
        lemma6BBlockAtAlpha x m l k H ν := by
  unfold lemma6LogDerivBlockAtAlpha lemma6ABlockAtAlpha
    lemma6BBlockAtAlpha
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d * lemma6LogDerivModulusAtAlpha d x m k ν) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d *
          ((4 * Real.log (x : ℝ) ^ 2) *
              lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) +
            lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (lemma6LogDerivModulusAtAlpha_le d hx m k ν)
        (lemma6LinearWeight_nonneg d)
    _ = ∑ d ∈ lemma6ModulusBlock x l,
          ((4 * Real.log (x : ℝ) ^ 2) *
              (lemma6LinearWeight d *
                lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) +
            lemma6LinearWeight d *
              lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = (4 * Real.log (x : ℝ) ^ 2) *
          (∑ d ∈ lemma6ModulusBlock x l,
            lemma6LinearWeight d *
              lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) +
        ∑ d ∈ lemma6ModulusBlock x l,
          lemma6LinearWeight d *
            lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- All characters over one dyadic modulus block, represented by a single
finite dependent index set. -/
noncomputable def lemma6CharacterBlock (x l : ℕ) :
    Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
  (lemma6ModulusBlock x l).sigma fun _d => Finset.univ

/-- The nonnegative base weight `|μ(d)|/d`, with nonprimitive characters
assigned weight zero.  The exceptional factor `3^ν(d)` remains separate
so equation (18) can absorb it. -/
noncomputable def lemma6PrimitiveBaseWeight
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  (|((ArithmeticFunction.moebius i.1 : ℤ) : ℝ)| / (i.1 : ℝ)) *
    if i.2.IsPrimitive then 1 else 0

theorem lemma6PrimitiveBaseWeight_nonneg
    (i : Σ d : ℕ, DirichletCharacter ℂ d) :
    0 ≤ lemma6PrimitiveBaseWeight i := by
  unfold lemma6PrimitiveBaseWeight
  positivity

/-- Norm of the actual prime-pair polynomial at a character-block index. -/
noncomputable def lemma6PairBlockNorm
    (x m k : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  ‖lemma6PairBlockPolynomial x m k s i.2‖

/-- Norm of `1-LS`, the second factor in the printed `A` integrand. -/
noncomputable def lemma6RemainderNorm
    (H : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  if hd : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hd⟩
    ‖1 - DirichletCharacter.LFunction i.2 s * lemma6MollifierAt H s i.2‖

/-- Norm of the Möbius mollifier in the `B` integrand. -/
noncomputable def lemma6MollifierNorm
    (H : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  ‖lemma6MollifierAt H s i.2‖

/-- Norm of `L'` in the `B` integrand. -/
noncomputable def lemma6LDerivNorm
    (s : ℂ) (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  if hd : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hd⟩
    ‖deriv (DirichletCharacter.LFunction i.2) s‖

/-- Formula (19), `A` part: weighted Cauchy--Schwarz on the actual
modulus/primitive-character block, with equation (18) absorbed into
`I_{l,x}`. -/
theorem lemma6_equation19_A_cauchy
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i *
          lemma6RemainderNorm H (lemma6AlphaPoint x ν) i) ^ 2 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i ^ 2) *
        ∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6RemainderNorm H (lemma6AlphaPoint x ν) i ^ 2 := by
  apply lemma6_weighted_cauchy_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν))
      (lemma6RemainderNorm H (lemma6AlphaPoint x ν)) hxlarge
  · intro i hi
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  · intro i hi
    exact lemma6PrimitiveBaseWeight_nonneg i

/-- Formula (19), `B` part: the weighted `2,4,4` Hölder inequality for
the prime-pair polynomial, mollifier, and `L'` fourth moments on `β+iν`. -/
theorem lemma6_equation19_B_holder
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
  apply lemma6_weighted_holder_244_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6PairBlockNorm x m k (lemma6BetaPoint x ν))
      (lemma6MollifierNorm H (lemma6BetaPoint x ν))
      (lemma6LDerivNorm (lemma6BetaPoint x ν)) hxlarge
  · intro i hi
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  · intro i hi
    exact lemma6PrimitiveBaseWeight_nonneg i
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    unfold lemma6LDerivNorm
    split_ifs <;> positivity

/-- Formula (20), `B` part: the same weighted `2,4,4` Hölder inequality,
but with the mollifier in the second moment and the pair polynomial in the
fourth moment.  This is the factor ordering printed across pages 12--13. -/
theorem lemma6_equation20_B_holder
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (lemma6_weighted_holder_244_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6MollifierNorm H (lemma6BetaPoint x ν))
      (lemma6LDerivNorm (lemma6BetaPoint x ν))
      (lemma6PairBlockNorm x m k (lemma6BetaPoint x ν)) hxlarge
      (by
        intro i hi
        rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
        exact hi.1)
      (by intro i hi; exact lemma6PrimitiveBaseWeight_nonneg i)
      (by intro i hi; exact norm_nonneg _)
      (by
        intro i hi
        unfold lemma6LDerivNorm
        split_ifs <;> positivity)
      (by intro i hi; exact norm_nonneg _))

end Chen
