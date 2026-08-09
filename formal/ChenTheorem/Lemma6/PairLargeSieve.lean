/-
The character-large-sieve input for the prime-pair polynomial in equations
(19) and (20).  The first step is the uniqueness of the ordered product
`p₁ p₂` on Chen's prime-pair range.
-/
import ChenTheorem.Lemma6.MomentConnection
import ChenTheorem.LargeSieve.Character

open Real
open scoped Classical

namespace Chen

theorem chenPair_fst_lt_snd
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) : q.1 < q.2 := by
  have hqdata := (Finset.mem_filter.mp hq).2
  rcases hqdata with ⟨hq1p, hq2p, hq1lo, hq1hi, hq2lo, hq2hi⟩
  have hreal : (q.1 : ℝ) < q.2 :=
    hq1hi.trans_lt hq2lo
  exact_mod_cast hreal

theorem pairProduct_injective_on_chenPairs
    {x : ℕ} {q r : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hr : r ∈ chenPairs x)
    (hprod : q.1 * q.2 = r.1 * r.2) : q = r := by
  have hqdata := (Finset.mem_filter.mp hq).2
  have hrdata := (Finset.mem_filter.mp hr).2
  rcases hqdata with ⟨hq1p, hq2p, hq1lo, hq1hi, hq2lo, hq2hi⟩
  rcases hrdata with ⟨hr1p, hr2p, hr1lo, hr1hi, hr2lo, hr2hi⟩
  have hdiv : q.1 ∣ r.1 * r.2 := by
    rw [← hprod]
    exact dvd_mul_right q.1 q.2
  rcases hq1p.dvd_mul.mp hdiv with hdiv | hdiv
  · have hfirst : q.1 = r.1 :=
      (Nat.prime_dvd_prime_iff_eq hq1p hr1p).mp hdiv
    have hsecond : q.2 = r.2 := by
      exact Nat.mul_left_cancel hq1p.pos (by simpa only [hfirst] using hprod)
    exact Prod.ext hfirst hsecond
  · have hcross : q.1 = r.2 :=
      (Nat.prime_dvd_prime_iff_eq hq1p hr2p).mp hdiv
    have hother : q.2 = r.1 := by
      exact Nat.mul_left_cancel hq1p.pos (by
        calc
          q.1 * q.2 = r.1 * r.2 := hprod
          _ = q.1 * r.1 := by rw [hcross]; ring)
    have hqr := chenPair_fst_lt_snd hq
    have hrr := chenPair_fst_lt_snd hr
    omega

/-- Real lower endpoint `2^k x^(13/30)` of the `k`-th pair-product block. -/
noncomputable def lemma6PairDyadicScale (x k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30)

/-- Integer lower endpoint used by the character large sieve. -/
noncomputable def lemma6PairLowerCutoff (x k : ℕ) : ℕ :=
  ⌊lemma6PairDyadicScale x k⌋₊

/-- Integer upper endpoint used by the character large sieve. -/
noncomputable def lemma6PairUpperCutoff (x k : ℕ) : ℕ :=
  ⌈lemma6PairDyadicScale x (k + 1)⌉₊

theorem lemma6PairLowerCutoff_le_upperCutoff (x k : ℕ) :
    lemma6PairLowerCutoff x k ≤ lemma6PairUpperCutoff x k := by
  have hxpow : 0 ≤ (x : ℝ) ^ ((13 : ℝ) / 30) :=
    Real.rpow_nonneg (by positivity) _
  have hlower :
      (lemma6PairLowerCutoff x k : ℝ) ≤ lemma6PairDyadicScale x k := by
    unfold lemma6PairLowerCutoff lemma6PairDyadicScale
    exact Nat.floor_le (by positivity)
  have hscale : lemma6PairDyadicScale x k ≤
      lemma6PairDyadicScale x (k + 1) := by
    unfold lemma6PairDyadicScale
    apply mul_le_mul_of_nonneg_right _ hxpow
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hupper : lemma6PairDyadicScale x (k + 1) ≤
      (lemma6PairUpperCutoff x k : ℝ) := by
    unfold lemma6PairUpperCutoff
    exact Nat.le_ceil _
  exact_mod_cast hlower.trans (hscale.trans hupper)

/-- Every admissible pair in block `k` has product in the integer interval
used for its character-large-sieve estimate. -/
theorem lemma6AdmissiblePairBlock_product_mem_Ioc
    {x m k : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ lemma6AdmissiblePairBlock x m k) :
    q.1 * q.2 ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
      (lemma6PairUpperCutoff x k) := by
  have hqpair : q ∈ lemma6PairBlock x k :=
    (Finset.mem_filter.mp hq).2
  have hqdata := (Finset.mem_filter.mp hqpair).2
  rw [Finset.mem_Ioc]
  constructor
  · apply (Nat.floor_lt (by
      unfold lemma6PairDyadicScale
      positivity)).2
    simpa only [lemma6PairDyadicScale] using hqdata.1
  · have hceil : lemma6PairDyadicScale x (k + 1) ≤
        (lemma6PairUpperCutoff x k : ℝ) := by
      unfold lemma6PairUpperCutoff
      exact Nat.le_ceil _
    exact_mod_cast (show ((q.1 * q.2 : ℕ) : ℝ) ≤
        lemma6PairDyadicScale x (k + 1) by
      simpa only [lemma6PairDyadicScale] using hqdata.2).trans hceil

/-- Coefficient obtained by grouping the pair polynomial by the product
`n = p₁p₂`. -/
noncomputable def lemma6PairCoefficient
    (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ _q ∈ pairs.filter (fun q => q.1 * q.2 = n),
    1 / ((n : ℂ) ^ s *
      (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))

/-- Regroup the pair polynomial as an ordinary Dirichlet polynomial on a
product interval. -/
theorem lemma6PairDirichletPolynomial_eq_sum_coeff
    {d M Q : ℕ} (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ)
    (χ : DirichletCharacter ℂ d)
    (hsupp : ∀ q ∈ pairs, q.1 * q.2 ∈ Finset.Ioc M Q) :
    lemma6PairDirichletPolynomial x pairs s χ =
      ∑ n ∈ Finset.Ioc M Q, lemma6PairCoefficient x pairs s n * χ n := by
  let prod : ℕ × ℕ → ℕ := fun q => q.1 * q.2
  let term : ℕ × ℕ → ℂ := fun q =>
    χ (q.1 * q.2 : ZMod d) /
      (((q.1 * q.2 : ℕ) : ℂ) ^ s *
        (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))
  have hfiber := Finset.sum_fiberwise_eq_sum_filter pairs (Finset.Ioc M Q)
    prod term
  rw [Finset.filter_eq_self.mpr (by
    intro q hq
    exact hsupp q hq)] at hfiber
  unfold lemma6PairDirichletPolynomial
  calc
    (∑ q ∈ pairs,
        χ (q.1 * q.2 : ZMod d) /
          (((q.1 * q.2 : ℕ) : ℂ) ^ s *
            (Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))) =
      ∑ n ∈ Finset.Ioc M Q,
        ∑ q ∈ pairs.filter (fun q => q.1 * q.2 = n), term q :=
      hfiber.symm
    _ = ∑ n ∈ Finset.Ioc M Q,
        lemma6PairCoefficient x pairs s n * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold lemma6PairCoefficient
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hprod := (Finset.mem_filter.mp hq).2
      dsimp only [term]
      rw [hprod]
      rw [← Nat.cast_mul, hprod]
      ring

/-- The actual `(k,m)` pair block in the interval required by the dyadic
character large sieve. -/
theorem lemma6PairBlockPolynomial_eq_sum_coeff
    {d : ℕ} (x m k : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ d) :
    lemma6PairBlockPolynomial x m k s χ =
      ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
        lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n * χ n := by
  unfold lemma6PairBlockPolynomial
  apply lemma6PairDirichletPolynomial_eq_sum_coeff
  intro q hq
  exact lemma6AdmissiblePairBlock_product_mem_Ioc hq

/-- On Chen's ordered prime-pair range, each product fibre contains at most
one pair. -/
theorem card_lemma6AdmissiblePairBlock_productFiber_le_one
    (x m k n : ℕ) :
    ((lemma6AdmissiblePairBlock x m k).filter
      (fun q => q.1 * q.2 = n)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro q r hq hr
  have hqmem := (Finset.mem_filter.mp hq)
  have hrmem := (Finset.mem_filter.mp hr)
  have hqchen : q ∈ chenPairs x :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp hqmem.1).1).1
  have hrchen : r ∈ chenPairs x :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp hrmem.1).1).1
  apply pairProduct_injective_on_chenPairs hqchen hrchen
  exact hqmem.2.trans hrmem.2.symm

/-- Uniqueness of the prime factorization removes any multiplicity loss
when the pair polynomial is regrouped by its product. -/
theorem norm_lemma6PairCoefficient_sq_le
    (x m k : ℕ) (s : ℂ) (n : ℕ) :
    ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 ≤
      ‖1 / ((n : ℂ) ^ s *
        (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))‖ ^ 2 := by
  let fiber := (lemma6AdmissiblePairBlock x m k).filter
    (fun q => q.1 * q.2 = n)
  have hcard := card_lemma6AdmissiblePairBlock_productFiber_le_one x m k n
  have hcases : fiber.card = 0 ∨ fiber.card = 1 := by
    dsimp only [fiber]
    omega
  rcases hcases with hzero | hone
  · have hfiber : fiber = ∅ := Finset.card_eq_zero.mp hzero
    simp [lemma6PairCoefficient, fiber, hfiber]
    positivity
  · obtain ⟨q, hfiber⟩ := Finset.card_eq_one.mp hone
    simp [lemma6PairCoefficient, fiber, hfiber]

/-- Raw character-large-sieve estimate for the actual prime-pair polynomial
on one modulus interval and one pair-product block. -/
theorem lemma6_pairPolynomial_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q x m k : ℕ) (s : ℂ), 1 ≤ D → D ≤ Q →
        ∑ d ∈ Finset.Ioc D Q, (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) ≤
          C * ((Q : ℝ) +
              ((lemma6PairUpperCutoff x k -
                lemma6PairLowerCutoff x k : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
              (lemma6PairUpperCutoff x k),
                ‖lemma6PairCoefficient x
                  (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q x m k s hD hDQ
  let M := lemma6PairLowerCutoff x k
  let U := lemma6PairUpperCutoff x k
  let N := U - M
  let a : ℕ → ℂ := fun n =>
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n
  have hMU : M ≤ U := lemma6PairLowerCutoff_le_upperCutoff x k
  have hMN : M + N = U := by
    dsimp only [N]
    exact Nat.add_sub_of_le hMU
  have hraw := hlarge D Q M N a hD hDQ
  simpa only [M, U, N, a, hMN,
    lemma6PairBlockPolynomial_eq_sum_coeff] using hraw

/-- The coefficient square sum has no product-fibre multiplicity loss. -/
theorem lemma6_pairCoefficient_sum_sq_le
    (x m k : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x
        (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
        ‖1 / ((n : ℂ) ^ s *
          (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact norm_lemma6PairCoefficient_sq_le x m k s n

/-- Dirichlet-convolution coefficient of the square of the pair polynomial
on one product block. -/
noncomputable def lemma6PairSquareCoefficient
    (x m k : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  let S := Finset.Ioc (lemma6PairLowerCutoff x k)
    (lemma6PairUpperCutoff x k)
  ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.1 *
      lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.2

/-- Exact expansion of the squared pair polynomial.  Its product support is
contained in `(0,U²]`, where `U` is the integer upper endpoint of the pair
block. -/
theorem lemma6PairBlockPolynomial_sq_eq_sum_coeff
    {d : ℕ} (x m k : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ d) :
    lemma6PairBlockPolynomial x m k s χ ^ 2 =
      ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        lemma6PairSquareCoefficient x m k s r * χ r := by
  let S := Finset.Ioc (lemma6PairLowerCutoff x k)
    (lemma6PairUpperCutoff x k)
  let P := S ×ˢ S
  let R := Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2)
  let a : ℕ → ℂ := fun n =>
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n
  let term : ℕ × ℕ → ℂ := fun p => a p.1 * a p.2 * χ (p.1 * p.2)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ R := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Ioc.mp hpmem.1
    have hp2 := Finset.mem_Ioc.mp hpmem.2
    rw [Finset.mem_Ioc]
    constructor
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa only [pow_two] using Nat.mul_le_mul hp1.2 hp2.2
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P R
    (fun p : ℕ × ℕ => p.1 * p.2) term
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  rw [lemma6PairBlockPolynomial_eq_sum_coeff]
  unfold lemma6PairSquareCoefficient
  dsimp only [S, P, R, a]
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k) ×ˢ
        Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
        (lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.1 *
          χ p.1) *
        (lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.2 *
          χ p.2)) =
      ∑ p ∈ P, term p := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [term, a]
      rw [map_mul]
      ring
    _ = ∑ r ∈ R,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = r), term p := hfiber.symm
    _ = ∑ r ∈ R,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = r),
          a p.1 * a p.2) * χ r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hprod := (Finset.mem_filter.mp hp).2
      dsimp only [term]
      have hcast : (p.1 : ZMod d) * (p.2 : ZMod d) = (r : ZMod d) := by
        rw [← Nat.cast_mul, hprod]
      rw [hcast]
    _ = ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        (let S := Finset.Ioc (lemma6PairLowerCutoff x k)
            (lemma6PairUpperCutoff x k)
          ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
            lemma6PairCoefficient x
                (lemma6AdmissiblePairBlock x m k) s p.1 *
              lemma6PairCoefficient x
                (lemma6AdmissiblePairBlock x m k) s p.2) * χ r := by rfl

/-- Primitive-character fourth moment of the actual pair polynomial. -/
noncomputable def lemma6PairFourthTerm
    (x m k q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 4)

/-- Write the pair fourth moment as the second moment of its squared
Dirichlet polynomial, ready for the large sieve in equation (20). -/
theorem lemma6PairFourthTerm_eq_squarePolynomial
    (x m k q : ℕ) (s : ℂ) :
    lemma6PairFourthTerm x m k q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
          lemma6PairSquareCoefficient x m k s r * χ r‖ ^ 2
      else 0 := by
  unfold lemma6PairFourthTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6PairBlockPolynomial_sq_eq_sum_coeff]
    rw [norm_pow]
    ring
  · simp [hp]

/-- Rewrite the pair fourth moment on the dependent character block. -/
theorem lemma6_pairFourth_characterBlock_eq
    {x l m k : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6PairFourthTerm x m k d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    lemma6PairFourthTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace `|μ(d)|/d` by `1/φ(d)` in the pair fourth moment. -/
theorem lemma6_pairFourth_characterBlock_le_inv_totient
    {x l m k : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6PairFourthTerm x m k d s := by
  rw [lemma6_pairFourth_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6PairFourthTerm x m k d s := by
    unfold lemma6PairFourthTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- Equation (20)'s pair-polynomial fourth moment, obtained by applying the
dyadic character large sieve to the squared polynomial of length `U²`. -/
theorem lemma6_pair_fourth_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l m k : ℕ) (s : ℂ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k s i ^ 4) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
              ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k s hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let U2 := lemma6PairUpperCutoff x k ^ 2
  let a : ℕ → ℂ := lemma6PairSquareCoefficient x m k s
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hraw := hlarge D Q 0 U2 a hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6PairFourthTerm x m k d s :=
      lemma6_pairFourth_characterBlock_le_inv_totient hxlog s
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ r ∈ Finset.Ioc 0 U2, a r * χ r‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6PairFourthTerm_eq_squarePolynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ r ∈ Finset.Ioc 0 U2, a r * χ r‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + (U2 : ℝ) / (D : ℝ)) *
          ∑ r ∈ Finset.Ioc 0 U2, ‖a r‖ ^ 2 := by
      simpa only [zero_add] using hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
          ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2 := by
      simp only [D, Q, U2, a, Nat.cast_pow]

/-- Rewrite the prime-pair second moment on the dependent character block
as a sum of primitive-character moments over its moduli. -/
theorem lemma6_pairSecond_characterBlock_eq
    {x l m k : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace `|μ(d)|/d` by the large-sieve weight `1/φ(d)` in the pair
second moment. -/
theorem lemma6_pairSecond_characterBlock_le_inv_totient
    {x l m k : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
  rw [lemma6_pairSecond_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ primSum d (fun χ =>
      ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
    unfold primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- The prime-pair second moment appearing in equation (19), now directly
bounded by the dyadic character large sieve on the actual modulus block. -/
theorem lemma6_pair_second_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l m k : ℕ) (s : ℂ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k s i ^ 2) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              ((lemma6PairUpperCutoff x k -
                lemma6PairLowerCutoff x k : ℕ) : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
              (lemma6PairUpperCutoff x k),
                ‖lemma6PairCoefficient x
                  (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by
  rcases lemma6_pairPolynomial_large_sieve with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k s hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hraw := hlarge D Q x m k s hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) :=
      lemma6_pairSecond_characterBlock_le_inv_totient hxlog s
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primSum, tsum_fintype]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
            ‖lemma6PairCoefficient x
              (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
            ‖lemma6PairCoefficient x
              (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by rfl

end Chen
