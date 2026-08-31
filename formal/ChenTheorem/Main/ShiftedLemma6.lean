import ChenTheorem.Main.ShiftedLemma5Arithmetic
import ChenTheorem.Lemma6.Core

open Filter Real MeasureTheory
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! # Fixed-shift analogue of Lemma 6

This file starts the conductor reduction for the primitive-character error.
The analytic scale remains `x`; only the unit phase is evaluated at `h` and
the outer sieve moduli are coprime to `h`.
-/

noncomputable def shiftedLemma6PrimitiveBlock
    (h x m l : ℕ) : ℂ :=
  primComplexSum l (fun χ =>
    starRingEnd ℂ (χ (h : ZMod l)) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) m),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))

/-- The `k`-th prime-pair piece with the fixed-shift character phase. -/
noncomputable def shiftedLemma6PrimitivePairBlock
    (h x m l k : ℕ) : ℂ :=
  primComplexSum l (fun χ =>
    starRingEnd ℂ (χ (h : ZMod l)) *
      ∑ q ∈ (lemma6AdmissiblePairs x m).filter
          (fun q => q ∈ lemma6PairBlock x k),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))

theorem shiftedLemma6PrimitiveBlock_mul_left
    (h x l m : ℕ) (_hl : 0 < l) :
    shiftedLemma6PrimitiveBlock h x (l * m) l =
      shiftedLemma6PrimitiveBlock h x m l := by
  letI : NeZero l := ⟨_hl.ne'⟩
  unfold shiftedLemma6PrimitiveBlock primComplexSum
  apply tsum_congr
  intro χ
  by_cases hχ : χ.IsPrimitive
  · rw [if_pos hχ, if_pos hχ]
    let S := (chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) m)
    let P := fun q : ℕ × ℕ => Nat.Coprime (q.1 * q.2) l
    have hfilter :
        (chenPairs x).filter
            (fun q => Nat.Coprime (q.1 * q.2) (l * m)) =
          S.filter P := by
      ext q
      simp only [S, P, Finset.mem_filter]
      rw [Nat.coprime_mul_iff_right]
      tauto
    rw [hfilter]
    have hzero :
        ∑ q ∈ S.filter (fun q => ¬P q),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                χ (q.1 * q.2 * n : ZMod l) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqnot : ¬Nat.Coprime (q.1 * q.2) l :=
        (Finset.mem_filter.mp hq).2
      apply Finset.sum_eq_zero
      intro n hn
      have hprodnot : ¬Nat.Coprime (q.1 * q.2 * n) l := by
        intro hprod
        exact hqnot (Nat.Coprime.of_dvd_left
          (by exact dvd_mul_right (q.1 * q.2) n) hprod)
      have hnonunit :
          ¬IsUnit ((q.1 * q.2 * n : ℕ) : ZMod l) := by
        intro hu
        exact hprodnot ((ZMod.isUnit_iff_coprime
          (q.1 * q.2 * n) l).1 hu)
      have hnonunit' :
          ¬IsUnit ((q.1 : ZMod l) * q.2 * n) := by
        simpa only [Nat.cast_mul] using hnonunit
      have hχzero : χ (q.1 * q.2 * n : ZMod l) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit'
      rw [hχzero, mul_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := S) (p := P)
      (f := fun q =>
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))
    rw [hzero, add_zero] at hsplit
    simpa only [S] using congrArg
      (fun z : ℂ => starRingEnd ℂ (χ (h : ZMod l)) * z) hsplit
  · rw [if_neg hχ, if_neg hχ]

theorem shiftedLemma6PrimitiveBlock_one_eq_two
    {h x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (l : ℕ) :
    shiftedLemma6PrimitiveBlock h x 1 l =
      shiftedLemma6PrimitiveBlock h x 2 l := by
  have hfilterOne :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 1) = chenPairs x := by
    simp
  have hfilterTwo :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 2) = chenPairs x := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    have hqdata := (Finset.mem_filter.mp hq).2
    have hq₁gt : 2 < q.1 := by
      exact_mod_cast hroot.trans_lt hqdata.2.2.1
    have hq₁odd : Odd q.1 := hqdata.1.odd_of_ne_two (by omega)
    have hq₂gtq₁ : q.1 < q.2 := by
      exact_mod_cast hqdata.2.2.2.1.trans_lt hqdata.2.2.2.2.1
    have hq₂odd : Odd q.2 := hqdata.2.1.odd_of_ne_two (by omega)
    exact (hq₁odd.mul hq₂odd).coprime_two_right
  unfold shiftedLemma6PrimitiveBlock
  rw [hfilterOne, hfilterTwo]

theorem shiftedLemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    {h x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    shiftedLemma6PrimitivePairBlock h x m l k =
      primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (h : ZMod l)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ∫ ν : ℝ,
              -(((x : ℂ) ^ lemma6AlphaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)) *
                lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))))) := by
  unfold shiftedLemma6PrimitivePairBlock
  apply congrArg (primComplexSum l)
  funext χ
  rw [show
    (lemma6AdmissiblePairs x m).filter
        (fun q => q ∈ lemma6PairBlock x k) =
      lemma6AdmissiblePairBlock x m k by rfl]
  rw [lemma6_finiteMellin_sum_eq_logDeriv_verticalIntegral
    hx hxlog (lemma6AdmissiblePairBlock x m k)
      (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ]
  rfl

theorem norm_shiftedLemma6PrimitivePairBlock_le_logDeriv_integral
    {h x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    ‖shiftedLemma6PrimitivePairBlock h x m l k‖ ≤
      (1 / (2 * Real.pi) : ℝ) *
        ∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let G : DirichletCharacter ℂ l → ℝ → ℂ := fun χ ν =>
    -(((x : ℂ) ^ lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)) *
      lemma6PairBlockPolynomial x m k
        (lemma6AlphaPoint x ν) χ *
      (deriv (DirichletCharacter.LFunction χ)
          (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ
          (lemma6AlphaPoint x ν)))
  let R : DirichletCharacter ℂ l → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hrepr := shiftedLemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    (h := h) (x := x) (l := l) hx hxlog m k
  change shiftedLemma6PrimitivePairBlock h x m l k =
    primComplexSum l (fun χ =>
      starRingEnd ℂ (χ (h : ZMod l)) *
        (c • ∫ ν : ℝ, G χ ν)) at hrepr
  rw [hrepr]
  unfold primComplexSum
  simp only [tsum_fintype]
  have hint (χ : DirichletCharacter ℂ l) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (integrable_lemma6PairLogDerivIntegrand hx hxlog
        (lemma6AdmissiblePairBlock x m k)
        (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ).norm
    · simp [R, hp]
  calc
    ‖∑ χ : DirichletCharacter ℂ l,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (h : ZMod l)) *
            (c • ∫ ν : ℝ, G χ ν)
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ l,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (h : ZMod l)) *
            (c • ∫ ν : ℝ, G χ ν)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ l,
        c * ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, norm_smul]
        have hc : ‖c‖ = c := Real.norm_of_nonneg (by
          dsimp only [c]
          positivity)
        rw [RCLike.norm_conj, hc]
        calc
          ‖χ (h : ZMod l)‖ * (c * ‖∫ ν : ℝ, G χ ν‖) ≤
              1 * (c * ∫ ν : ℝ, ‖G χ ν‖) := by
            gcongr
            · exact χ.norm_le_one h
            · exact norm_integral_le_integral_norm _
          _ = c * ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = c * ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ l, R χ ν := by
      rw [← Finset.mul_sum]
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = (1 / (2 * Real.pi) : ℝ) *
        ∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖) := by
      dsimp only [c]
      congr 1
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G primSum
      simp only [tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

theorem shiftedLemma6PrimitivePairBlock_eq_A_alpha_add_B_beta
    {h x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    shiftedLemma6PrimitivePairBlock h x m d k =
      primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (h : ZMod d)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ((∫ ν : ℝ,
                lemma6AContourIntegrand x m k H χ
                  (lemma6AlphaPoint x ν)) +
              ∫ ν : ℝ,
                lemma6BContourIntegrand x m k H χ
                  (lemma6BetaPoint x ν)))) := by
  have hrepr := shiftedLemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    (h := h) (x := x) (l := d) hx (by linarith) m k
  rw [hrepr]
  unfold primComplexSum
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    let U : ℝ → ℂ := fun ν =>
      lemma6LogDerivContourIntegrand x m k χ (lemma6AlphaPoint x ν)
    let A : ℝ → ℂ := fun ν =>
      lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
    let Ba : ℝ → ℂ := fun ν =>
      lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
    let Bb : ℝ → ℂ := fun ν =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)
    have hU : Integrable U := by
      simpa only [U, lemma6LogDerivContourIntegrand,
        lemma6PairBlockPolynomial] using
        integrable_lemma6PairLogDerivIntegrand hx (by linarith)
          (lemma6AdmissiblePairBlock x m k)
          (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ
    have hBa : Integrable Ba := by
      simpa only [Ba] using
        integrable_lemma6BContourIntegrand_alpha
          hd hx (by linarith) m k H χ hp
    have hpoint : ∀ ν : ℝ, U ν = A ν + Ba ν := by
      intro ν
      exact lemma6LogDerivContourIntegrand_alpha_eq_A_add_B
        hx m k H χ ν
    have hAeq : A = fun ν => U ν - Ba ν := by
      funext ν
      rw [hpoint ν]
      abel
    have hA : Integrable A := by
      rw [hAeq]
      exact hU.sub hBa
    have hshift : (∫ ν : ℝ, Ba ν) = ∫ ν : ℝ, Bb ν := by
      simpa only [Ba, Bb] using
        lemma6BContour_verticalIntegral_eq hd hx hxlog m k H hp
          (hhor χ hp) hBa (hβ χ hp)
    have hint : (∫ ν : ℝ, U ν) =
        (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν := by
      calc
        (∫ ν : ℝ, U ν) = ∫ ν : ℝ, A ν + Ba ν := by
          apply integral_congr_ae
          exact ae_of_all _ hpoint
        _ = (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Ba ν :=
          MeasureTheory.integral_add hA hBa
        _ = (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν := by rw [hshift]
    change starRingEnd ℂ (χ (h : ZMod d)) *
        ((1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, U ν) =
      starRingEnd ℂ (χ (h : ZMod d)) *
        ((1 / (2 * Real.pi) : ℝ) •
          ((∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν))
    rw [hint]
  · simp [hp]

theorem norm_primComplexSum_lemma6BContour_beta_integral_le_at
    {d x : ℕ} [NeZero d] (a m k H : ℕ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    ‖primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (a : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ
              (lemma6BetaPoint x ν))‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν) := by
  let G : DirichletCharacter ℂ d → ℝ → ℂ := fun χ ν =>
    lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)
  let R : DirichletCharacter ℂ d → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hint (χ : DirichletCharacter ℂ d) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (hβ χ hp).norm
    · simp [R, hp]
  unfold primComplexSum
  simp only [tsum_fintype]
  calc
    ‖∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (a : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ d,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (a : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ d, ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, RCLike.norm_conj]
        calc
          ‖χ (a : ZMod d)‖ * ‖∫ ν : ℝ, G χ ν‖ ≤
              1 * ∫ ν : ℝ, ‖G χ ν‖ := by
            gcongr
            · exact χ.norm_le_one a
            · exact norm_integral_le_integral_norm _
          _ = ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ d, R χ ν := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν) := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G lemma6BContourIntegrand lemma6BModulusTotal
      simp only [dif_neg (NeZero.ne d), lemma6BModulus,
        lemma6PairBlockPolynomial, primSum, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

theorem norm_primComplexSum_lemma6AContour_alpha_integral_le_at
    {d x : ℕ} [NeZero d] (a m k H : ℕ)
    (hA : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν))) :
    ‖primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (a : ZMod d)) *
          ∫ ν : ℝ,
            lemma6AContourIntegrand x m k H χ
              (lemma6AlphaPoint x ν))‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
  let G : DirichletCharacter ℂ d → ℝ → ℂ := fun χ ν =>
    lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
  let R : DirichletCharacter ℂ d → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hint (χ : DirichletCharacter ℂ d) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (hA χ hp).norm
    · simp [R, hp]
  unfold primComplexSum
  simp only [tsum_fintype]
  calc
    ‖∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (a : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ d,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (a : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ d, ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, RCLike.norm_conj]
        calc
          ‖χ (a : ZMod d)‖ * ‖∫ ν : ℝ, G χ ν‖ ≤
              1 * ∫ ν : ℝ, ‖G χ ν‖ := by
            gcongr
            · exact χ.norm_le_one a
            · exact norm_integral_le_integral_norm _
          _ = ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ d, R χ ν := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G lemma6AContourIntegrand lemma6RawAModulus
      simp only [lemma6PairBlockPolynomial, primSum, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

theorem norm_shiftedLemma6PrimitivePairBlock_le_A_alpha_add_B_beta
    {h x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    ‖shiftedLemma6PrimitivePairBlock h x m d k‖ ≤
      (1 / (2 * Real.pi) : ℝ) *
        ((∫ ν : ℝ,
            ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
                lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6AlphaPoint x ν)‖ *
              lemma6RawAModulus (d := d) x H
                (lemma6AdmissiblePairBlock x m k)
                (lemma6AlphaPoint x ν)) +
          ∫ ν : ℝ,
            ‖(x : ℂ) ^ lemma6BetaPoint x ν *
                lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6BetaPoint x ν)‖ *
              lemma6BModulusTotal d x m k H
                (lemma6BetaPoint x ν)) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let PA : ℂ := primComplexSum d (fun χ =>
    starRingEnd ℂ (χ (h : ZMod d)) *
      ∫ ν : ℝ,
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν))
  let PB : ℂ := primComplexSum d (fun χ =>
    starRingEnd ℂ (χ (h : ZMod d)) *
      ∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))
  have hAint : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) := by
    intro χ hp
    exact integrable_lemma6AContourIntegrand_alpha_of_B
      hx (by linarith) m k H χ
        (integrable_lemma6BContourIntegrand_alpha
          hd hx (by linarith) m k H χ hp)
  have hPA : ‖PA‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
    exact norm_primComplexSum_lemma6AContour_alpha_integral_le_at
      h m k H hAint
  have hPB : ‖PB‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H
            (lemma6BetaPoint x ν) := by
    exact norm_primComplexSum_lemma6BContour_beta_integral_le_at
      h m k H hβ
  have hdecomp := shiftedLemma6PrimitivePairBlock_eq_A_alpha_add_B_beta
    (h := h) hd hx hxlog m k H hhor hβ
  have hlinear : shiftedLemma6PrimitivePairBlock h x m d k =
      (c : ℂ) * (PA + PB) := by
    rw [hdecomp]
    unfold PA PB primComplexSum
    simp only [tsum_fintype]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro χ hχmem
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true, RCLike.real_smul_eq_coe_mul]
      dsimp only [c]
      simp only [mul_add, add_mul, mul_assoc, mul_comm]
      rfl
    · simp [hp]
  rw [hlinear, norm_mul]
  have hc : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    dsimp only [c]
    positivity
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [c]; positivity)
  exact (norm_add_le PA PB).trans (add_le_add hPA hPB)

theorem shiftedLemma6PrimitiveBlock_eq_sum_pairBlocks
    {h x m l : ℕ} (hx : 1 ≤ x) :
    shiftedLemma6PrimitiveBlock h x m l =
      ∑ k ∈ lemma6PairBlockIndices x m,
        shiftedLemma6PrimitivePairBlock h x m l k := by
  let P := lemma6AdmissiblePairs x m
  let K := lemma6PairBlockIndices x m
  let G : (ℕ × ℕ) → DirichletCharacter ℂ l → ℂ := fun q χ =>
    ∑ n ∈ smoothedMIndices x q,
      (smoothedMKernel x q n : ℂ) *
        χ (q.1 * q.2 * n : ZMod l)
  have hpair (χ : DirichletCharacter ℂ l) :
      ∑ q ∈ P, G q χ =
        ∑ k ∈ K,
          ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k),
            G q χ := by
    have hfiber := Finset.sum_fiberwise_eq_sum_filter P K
      (lemma6PairBlockIndex x) (fun q => G q χ)
    rw [Finset.filter_eq_self.mpr] at hfiber
    · exact hfiber.symm
    · intro q hq
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hfibereq (k : ℕ) :
      P.filter (fun q => lemma6PairBlockIndex x q = k) =
        P.filter (fun q => q ∈ lemma6PairBlock x k) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqP, hindex⟩
      have hqchen : q ∈ chenPairs x :=
        (Finset.mem_filter.mp hqP).1
      obtain ⟨j, hj⟩ := exists_mem_lemma6PairBlock hx hqchen
      have hcanonical := lemma6PairBlockIndex_mem ⟨j, hj⟩
      rw [hindex] at hcanonical
      exact ⟨hqP, hcanonical⟩
    · rintro ⟨hqP, hqblock⟩
      exact ⟨hqP, lemma6PairBlockIndex_eq hqblock⟩
  unfold shiftedLemma6PrimitiveBlock shiftedLemma6PrimitivePairBlock
  change primComplexSum l (fun χ =>
      starRingEnd ℂ (χ (h : ZMod l)) * ∑ q ∈ P, G q χ) =
      ∑ k ∈ K, primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (h : ZMod l)) *
          ∑ q ∈ P.filter (fun q => q ∈ lemma6PairBlock x k), G q χ)
  simp_rw [← hfibereq]
  have hdecomp (χ : DirichletCharacter ℂ l) :
      starRingEnd ℂ (χ (h : ZMod l)) * ∑ q ∈ P, G q χ =
        ∑ k ∈ K, starRingEnd ℂ (χ (h : ZMod l)) *
          ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k),
            G q χ := by
    rw [hpair, Finset.mul_sum]
  rw [show (fun χ : DirichletCharacter ℂ l =>
      starRingEnd ℂ (χ (h : ZMod l)) * ∑ q ∈ P, G q χ) =
      (fun χ => ∑ k ∈ K, starRingEnd ℂ (χ (h : ZMod l)) *
        ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k), G q χ) by
    funext χ
    exact hdecomp χ]
  unfold primComplexSum
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
  · simp only [hp, if_false, Finset.sum_const_zero]

theorem shiftedLemma6_divisor_cofactor_data
    {h x d l : ℕ} (hd : Squarefree d) (hl : l ∈ d.divisors) :
    lemma6TotientWeight d =
        lemma6TotientWeight l * lemma6TotientWeight (d / l) ∧
      shiftedLemma6PrimitiveBlock h x d l =
        shiftedLemma6PrimitiveBlock h x (d / l) l := by
  have hld : l ∣ d := Nat.dvd_of_mem_divisors hl
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp hl).2
  have hlpos : 0 < l :=
    Nat.pos_of_dvd_of_pos hld (Nat.pos_of_ne_zero hd0)
  have hquotpos : 0 < d / l := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld) hlpos
  have hprod : l * (d / l) = d := Nat.mul_div_cancel' hld
  have hcop : l.Coprime (d / l) :=
    Nat.coprime_of_squarefree_mul (hprod.symm ▸ hd)
  constructor
  · calc
      lemma6TotientWeight d =
          lemma6TotientWeight (l * (d / l)) := congrArg _ hprod.symm
      _ = lemma6TotientWeight l * lemma6TotientWeight (d / l) :=
        lemma6TotientWeight_mul hlpos.ne' hquotpos.ne' hcop
  · calc
      shiftedLemma6PrimitiveBlock h x d l =
          shiftedLemma6PrimitiveBlock h x (l * (d / l)) l :=
        congrArg (fun m => shiftedLemma6PrimitiveBlock h x m l)
          hprod.symm
      _ = shiftedLemma6PrimitiveBlock h x (d / l) l :=
        shiftedLemma6PrimitiveBlock_mul_left h x l (d / l) hlpos

theorem shiftedPrimitiveCharacterContribution_eq_sum_primitive
    {h x d : ℕ} (hd : 0 < d) :
    shiftedPrimitiveCharacterContribution h x d =
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else shiftedLemma6PrimitiveBlock h x d k.1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  unfold shiftedPrimitiveCharacterContribution nontrivialCharSum
  rw [dif_neg hd.ne', sum_characters_eq_sum_primitiveLifts,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2) hd).ne'⟩
  by_cases hkone : k.1 = 1
  · rw [if_pos hkone]
    apply Finset.sum_eq_zero
    intro ψ hψ
    rw [if_pos]
    change DirichletCharacter.changeLevel
        (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1
    rw [DirichletCharacter.changeLevel_eq_one_iff]
    apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    exact ψ.2.trans hkone
  · rw [if_neg hkone]
    unfold shiftedLemma6PrimitiveBlock primComplexSum
    rw [← sum_primitive_subtype_eq_tsum]
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hliftne : primitiveLift d ⟨k, ψ⟩ ≠ 1 := by
      change DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors k.2) ψ.1 ≠ 1
      intro hliftone
      have hψone : ψ.1 = 1 := by
        exact (DirichletCharacter.changeLevel_eq_one_iff
          (R := ℂ) (Nat.dvd_of_mem_divisors k.2)).mp hliftone
      apply hkone
      have hcond : ψ.1.conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp hψone
      exact ψ.2.symm.trans hcond
    rw [if_neg hliftne]
    change
      starRingEnd ℂ ((primitiveLift d ⟨k, ψ⟩).primitiveCharacter h) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                (primitiveLift d ⟨k, ψ⟩).primitiveCharacter
                  (q.1 * q.2 * n) =
        starRingEnd ℂ (ψ.1 h) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                ψ.1 (q.1 * q.2 * n)
    rw [primitiveLift_primitiveCharacter_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro n hn
    have happ := primitiveLift_primitiveCharacter_apply
      d ⟨k, ψ⟩ (q.1 * q.2 * n)
    simpa only [Nat.cast_mul] using congrArg
      (fun z : ℂ => (smoothedMKernel x q n : ℂ) * z) happ

theorem shiftedPrimitiveCharacterContribution_norm_le_sum_primitive
    {h x d : ℕ} (hd : 0 < d) :
    ‖shiftedPrimitiveCharacterContribution h x d‖ ≤
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖ := by
  rw [shiftedPrimitiveCharacterContribution_eq_sum_primitive hd]
  calc
    ‖∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else shiftedLemma6PrimitiveBlock h x d k.1‖ ≤
      ∑ k : ↥d.divisors,
        ‖if k.1 = 1 then 0
          else shiftedLemma6PrimitiveBlock h x d k.1‖ :=
      norm_sum_le _ _
    _ = ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkone : k.1 = 1 <;> simp [hkone]

noncomputable def shiftedLemma6ConductorMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    lemma6TotientWeight d *
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖

theorem shiftedMTwo_le_shiftedLemma6ConductorMajorant
    (h x : ℕ) (ε : ℝ) :
    shiftedMTwo h x ε ≤ shiftedLemma6ConductorMajorant h x ε := by
  unfold shiftedMTwo shiftedLemma6ConductorMajorant
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by
    have hddata := (Finset.mem_filter.mp hd).2
    omega
  apply mul_le_mul_of_nonneg_left
    (shiftedPrimitiveCharacterContribution_norm_le_sum_primitive hdpos)
  exact lemma6TotientWeight_nonneg d

theorem divisor_mem_shiftedSieveModuli
    {h x l d : ℕ} {ε : ℝ}
    (hd : d ∈ shiftedSieveModuli h x ε)
    (hlpos : 0 < l) (hld : l ∣ d) :
    l ∈ shiftedSieveModuli h x ε := by
  rw [shiftedSieveModuli, Finset.mem_filter] at hd ⊢
  have hldle : l ≤ d := Nat.le_of_dvd (by omega) hld
  refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hldle
      (Finset.mem_range.mp hd.1)), ?_⟩
  refine ⟨hlpos, Nat.Coprime.of_dvd_left hld hd.2.2.1, ?_⟩
  exact (by exact_mod_cast hldle : (l : ℝ) ≤ d).trans hd.2.2.2

noncomputable def shiftedLemma6SplitConductorMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    if _hd : Squarefree d then
      ∑ k ∈ d.divisors,
        if k = 1 then 0
        else lemma6TotientWeight (d / k) * lemma6TotientWeight k *
          ‖shiftedLemma6PrimitiveBlock h x (d / k) k‖
    else 0

noncomputable def shiftedLemma6SplitPairRange
    (h x : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((shiftedSieveModuli h x ε).filter Squarefree).biUnion
    Nat.divisorsAntidiagonal

noncomputable def shiftedLemma6SplitPairTerm
    (h x : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.2 = 1 then 0
  else lemma6TotientWeight p.1 * lemma6TotientWeight p.2 *
    ‖shiftedLemma6PrimitiveBlock h x p.1 p.2‖

theorem shiftedLemma6SplitPairTerm_nonneg
    (h x : ℕ) (p : ℕ × ℕ) :
    0 ≤ shiftedLemma6SplitPairTerm h x p := by
  unfold shiftedLemma6SplitPairTerm
  split_ifs
  · positivity
  · exact mul_nonneg
      (mul_nonneg (lemma6TotientWeight_nonneg p.1)
        (lemma6TotientWeight_nonneg p.2)) (norm_nonneg _)

theorem shiftedLemma6ConductorMajorant_eq_split
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6ConductorMajorant h x ε =
      shiftedLemma6SplitConductorMajorant h x ε := by
  unfold shiftedLemma6ConductorMajorant
    shiftedLemma6SplitConductorMajorant
  apply Finset.sum_congr rfl
  intro d hdmem
  by_cases hdsq : Squarefree d
  · rw [dif_pos hdsq, Finset.mul_sum, ← d.divisors.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkone : k.1 = 1
    · simp [hkone]
    · rw [if_neg hkone, if_neg hkone]
      have hdata := shiftedLemma6_divisor_cofactor_data
        (h := h) (x := x) hdsq k.2
      rw [hdata.1, hdata.2]
      ring
  · rw [dif_neg hdsq]
    have hweight : lemma6TotientWeight d = 0 := by
      unfold lemma6TotientWeight
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
      norm_num
    rw [hweight, zero_mul]

theorem shiftedLemma6SplitConductorMajorant_eq_pairSum
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6SplitConductorMajorant h x ε =
      ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
        shiftedLemma6SplitPairTerm h x p := by
  have hdisj : Set.PairwiseDisjoint
      ((shiftedSieveModuli h x ε).filter Squarefree)
      Nat.divisorsAntidiagonal := by
    intro d₁ hd₁ d₂ hd₂ hdne
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have hprod₁ := (Nat.mem_divisorsAntidiagonal.mp hp₁).1
    have hprod₂ := (Nat.mem_divisorsAntidiagonal.mp hp₂).1
    exact hdne (hprod₁.symm.trans hprod₂)
  calc
    shiftedLemma6SplitConductorMajorant h x ε =
        ∑ d ∈ (shiftedSieveModuli h x ε).filter Squarefree,
          ∑ p ∈ d.divisorsAntidiagonal,
            shiftedLemma6SplitPairTerm h x p := by
      unfold shiftedLemma6SplitConductorMajorant
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdsq : Squarefree d
      · rw [dif_pos hdsq, if_pos hdsq]
        rw [← Nat.sum_divisorsAntidiagonal'
          (f := fun m k =>
            if k = 1 then 0
            else lemma6TotientWeight m * lemma6TotientWeight k *
              ‖shiftedLemma6PrimitiveBlock h x m k‖)]
        unfold shiftedLemma6SplitPairTerm
        rfl
      · rw [dif_neg hdsq, if_neg hdsq]
    _ = ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
          shiftedLemma6SplitPairTerm h x p := by
      unfold shiftedLemma6SplitPairRange
      exact (Finset.sum_biUnion hdisj).symm

theorem shiftedLemma6SplitPairRange_subset
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6SplitPairRange h x ε ⊆
      shiftedSieveModuli h x ε ×ˢ shiftedSieveModuli h x ε := by
  intro p hp
  rw [shiftedLemma6SplitPairRange, Finset.mem_biUnion] at hp
  obtain ⟨d, hd, hp⟩ := hp
  have hdmem : d ∈ shiftedSieveModuli h x ε :=
    (Finset.mem_filter.mp hd).1
  have hp₁pos : 0 < p.1 := Nat.pos_of_ne_zero
    (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
  have hp₂pos : 0 < p.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
  rw [Finset.mem_product]
  exact ⟨divisor_mem_shiftedSieveModuli hdmem hp₁pos
      (Nat.dvd_of_mem_divisors
        (Nat.fst_mem_divisors_of_mem_antidiagonal hp)),
    divisor_mem_shiftedSieveModuli hdmem hp₂pos
      (Nat.dvd_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal hp))⟩

noncomputable def shiftedLemma6IndependentMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ shiftedSieveModuli h x ε ×ˢ shiftedSieveModuli h x ε,
    shiftedLemma6SplitPairTerm h x p

theorem shiftedLemma6IndependentMajorant_eq_bisum
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6IndependentMajorant h x ε =
      ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ∑ l ∈ shiftedSieveModuli h x ε,
            if l = 1 then 0
            else lemma6TotientWeight l *
              ‖shiftedLemma6PrimitiveBlock h x m l‖ := by
  unfold shiftedLemma6IndependentMajorant
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  unfold shiftedLemma6SplitPairTerm
  by_cases hlone : l = 1
  · simp [hlone]
  · simp only [hlone, ↓reduceIte]
    ring

theorem shiftedMTwo_le_shiftedLemma6IndependentMajorant
    (h x : ℕ) (ε : ℝ) :
    shiftedMTwo h x ε ≤
      shiftedLemma6IndependentMajorant h x ε := by
  calc
    shiftedMTwo h x ε ≤ shiftedLemma6ConductorMajorant h x ε :=
      shiftedMTwo_le_shiftedLemma6ConductorMajorant h x ε
    _ = shiftedLemma6SplitConductorMajorant h x ε :=
      shiftedLemma6ConductorMajorant_eq_split h x ε
    _ = ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
        shiftedLemma6SplitPairTerm h x p :=
      shiftedLemma6SplitConductorMajorant_eq_pairSum h x ε
    _ ≤ shiftedLemma6IndependentMajorant h x ε := by
      unfold shiftedLemma6IndependentMajorant
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (shiftedLemma6SplitPairRange_subset h x ε)
      intro p hp hnot
      exact shiftedLemma6SplitPairTerm_nonneg h x p

noncomputable def shiftedLemma6NmTerm
    (h x : ℕ) (m l : ℕ) : ℝ :=
  lemma6LinearWeight l * ‖shiftedLemma6PrimitiveBlock h x m l‖

theorem shiftedLemma6NmTerm_nonneg (h x m l : ℕ) :
    0 ≤ shiftedLemma6NmTerm h x m l := by
  unfold shiftedLemma6NmTerm
  exact mul_nonneg (lemma6LinearWeight_nonneg l) (norm_nonneg _)

noncomputable def shiftedLemma6Nm
    (h x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ (shiftedSieveModuli h x ε).erase 1,
    shiftedLemma6NmTerm h x m l

theorem shiftedLemma6Nm_nonneg (h x : ℕ) (ε : ℝ) (m : ℕ) :
    0 ≤ shiftedLemma6Nm h x ε m := by
  unfold shiftedLemma6Nm
  apply Finset.sum_nonneg
  intro l hl
  exact shiftedLemma6NmTerm_nonneg h x m l

theorem shiftedLemma6Nm_one_eq_two
    {h x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (ε : ℝ) :
    shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2 := by
  unfold shiftedLemma6Nm shiftedLemma6NmTerm
  apply Finset.sum_congr rfl
  intro l hl
  rw [shiftedLemma6PrimitiveBlock_one_eq_two hroot l]

theorem eventually_shiftedLemma6Nm_one_eq_two
    (h : ℕ) (ε : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2 := by
  have hrootReal :
      ∀ᶠ y : ℝ in atTop, (2 : ℝ) ≤ y ^ ((1 : ℝ) / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 2)
  have hrootNat :
      ∀ᶠ x : ℕ in atTop,
        (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) :=
    tendsto_natCast_atTop_atTop.eventually hrootReal
  filter_upwards [hrootNat] with x hx
  exact shiftedLemma6Nm_one_eq_two hx ε

private theorem shifted_sum_ite_one_eq_sum_erase
    (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ S, (if l = 1 then 0 else f l) =
      ∑ l ∈ S.erase 1, f l := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases ha1 : a = 1
      · subst a
        simp [ha, ih]
      · rw [Finset.erase_insert_of_ne ha1]
        simp [ha, ha1, ih]

theorem shiftedLemma6TotientWeight_le_log_mul_linearWeight
    {h x d : ℕ} {ε : ℝ}
    (hd : d ∈ shiftedSieveModuli h x ε) (hd2 : 2 ≤ d) :
    lemma6TotientWeight d ≤
      (2 / Real.log 2) * Real.log x * lemma6LinearWeight d := by
  by_cases hdsq : Squarefree d
  · have hdx : d ≤ x := by
      have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
      omega
    have hratio := (totient_ratio_le_card_succ hdsq).trans
      (primeFactors_card_succ_le_log hdsq hd2)
    have hlog : Real.log d ≤ Real.log x := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hdx)
    have hconst : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
    have hratio' : (d : ℝ) / (Nat.totient d : ℝ) ≤
        (2 / Real.log 2) * Real.log x :=
      hratio.trans (mul_le_mul_of_nonneg_left hlog hconst)
    have htotpos : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    unfold lemma6TotientWeight lemma6LinearWeight
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d * (Nat.totient d : ℝ)⁻¹ =
          ((d : ℝ) / (Nat.totient d : ℝ)) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        field_simp
      _ ≤ ((2 / Real.log 2) * Real.log x) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right hratio'
        positivity
      _ = (2 / Real.log 2) * Real.log x *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by ring
  · unfold lemma6TotientWeight lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
    norm_num

theorem shiftedLemma6_inner_sum_le_nm
    {h x m : ℕ} {ε : ℝ} :
    (∑ l ∈ shiftedSieveModuli h x ε,
        if l = 1 then 0
        else lemma6TotientWeight l *
          ‖shiftedLemma6PrimitiveBlock h x m l‖) ≤
      (2 / Real.log 2) * Real.log x * shiftedLemma6Nm h x ε m := by
  rw [shifted_sum_ite_one_eq_sum_erase]
  unfold shiftedLemma6Nm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlmem : l ∈ shiftedSieveModuli h x ε :=
    Finset.mem_of_mem_erase hl
  have hl2 : 2 ≤ l := by
    have hlne : l ≠ 1 := Finset.ne_of_mem_erase hl
    have hlpos := (Finset.mem_filter.mp hlmem).2.1
    omega
  unfold shiftedLemma6NmTerm
  calc
    lemma6TotientWeight l *
        ‖shiftedLemma6PrimitiveBlock h x m l‖ ≤
      ((2 / Real.log 2) * Real.log x * lemma6LinearWeight l) *
        ‖shiftedLemma6PrimitiveBlock h x m l‖ := by
      exact mul_le_mul_of_nonneg_right
        (shiftedLemma6TotientWeight_le_log_mul_linearWeight hlmem hl2)
        (norm_nonneg _)
    _ = (2 / Real.log 2) * Real.log x *
        (lemma6LinearWeight l *
          ‖shiftedLemma6PrimitiveBlock h x m l‖) := by ring

private noncomputable def shiftedInvNatTwist
    (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else f n / (n : ℝ)
  map_zero' := if_pos rfl

@[simp] private theorem shiftedInvNatTwist_apply
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    shiftedInvNatTwist f n =
      if n = 0 then 0 else f n / (n : ℝ) := rfl

private theorem shiftedInvNatTwist_mul
    (f g : ArithmeticFunction ℝ) :
    shiftedInvNatTwist (f * g) =
      shiftedInvNatTwist f * shiftedInvNatTwist g := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  change
    (if n = 0 then 0 else
      (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) / (n : ℝ)) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 = 0 then 0 else f p.1 / (p.1 : ℝ)) *
          (if p.2 = 0 then 0 else g p.2 / (p.2 : ℝ))
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
    have hp₁ : p.1 ≠ 0 :=
      Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hp₂ : p.2 ≠ 0 :=
      Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    simp only [hp₁, hp₂, if_false]
    rw [← hpdata.1]
    push_cast
    field_simp

private theorem shiftedPartialSum_mul_le_mul
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (f * g) n ≤
      (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
  calc
    ∑ p ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter
        (fun p => p.1 * p.2 ≤ N), f p.1 * g p.2 ≤
      ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N,
        f p.1 * g p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro p hp hnot
      exact mul_nonneg (hf p.1) (hg p.2)
    _ = (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

private theorem shiftedInvNatTwist_zeta_nonneg (n : ℕ) :
    0 ≤ shiftedInvNatTwist
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : n = 0
  · simp [shiftedInvNatTwist, hn]
  · simp [shiftedInvNatTwist, hn, ArithmeticFunction.zeta_apply]

private theorem sum_shiftedInvNatTwist_zeta (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        shiftedInvNatTwist
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n =
      (harmonic N : ℝ) := by
  have hfin : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp
    omega
  rw [hfin, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  simp [shiftedInvNatTwist, hnpos.ne',
    ArithmeticFunction.zeta_apply, Rat.cast_inv, Rat.cast_natCast]

private theorem sum_shiftedInvNatTwist_zeta_cube_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((shiftedInvNatTwist
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) n ≤
      (harmonic N : ℝ) ^ 3 := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hz : ∀ n, 0 ≤ z n := shiftedInvNatTwist_zeta_nonneg
  have hzz : ∀ n, 0 ≤ (z * z) n := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hz p.1) (hz p.2)
  calc
    ∑ n ∈ Finset.Ioc 0 N, (z ^ 3) n =
        ∑ n ∈ Finset.Ioc 0 N, ((z * z) * z) n := by
      rw [pow_succ, pow_two]
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (z * z) n) *
        ∑ n ∈ Finset.Ioc 0 N, z n :=
      shiftedPartialSum_mul_le_mul (z * z) z hzz hz N
    _ ≤ ((∑ n ∈ Finset.Ioc 0 N, z n) *
        ∑ n ∈ Finset.Ioc 0 N, z n) *
          ∑ n ∈ Finset.Ioc 0 N, z n := by
      apply mul_le_mul_of_nonneg_right
        (shiftedPartialSum_mul_le_mul z z hz hz N)
      exact Finset.sum_nonneg fun n hn => hz n
    _ = (harmonic N : ℝ) ^ 3 := by
      rw [show ∑ n ∈ Finset.Ioc 0 N, z n =
          (harmonic N : ℝ) by exact sum_shiftedInvNatTwist_zeta N]
      ring

private theorem shifted_zeta_cube_apply_squarefree_real
    {d : ℕ} (hd : Squarefree d) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      (3 : ℝ) ^ d.primeFactors.card := by
  have hnat :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) d =
        3 ^ d.primeFactors.card := by
    rw [show (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3 =
        ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta by
      have hz :
          (ArithmeticFunction.zeta : ArithmeticFunction ℕ) *
              ArithmeticFunction.zeta = ArithmeticFunction.sigma 0 := by
        simpa only [ArithmeticFunction.pow_zero_eq_zeta] using
          (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 0))
      rw [pow_succ, pow_two, hz]]
    rw [← ArithmeticFunction.isMultiplicative_sigma.prodPrimeFactors_add_of_squarefree
      ArithmeticFunction.isMultiplicative_zeta hd]
    rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hs := ArithmeticFunction.sigma_zero_apply_prime_pow
      (i := 1) hpprime
    norm_num at hs
    rw [ArithmeticFunction.add_apply, hs]
    simp [ArithmeticFunction.zeta_apply, hpprime.ne_zero]
  have hcoe :
      (↑((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) :
          ArithmeticFunction ℝ) =
        (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ) ^ 3 := by
    rw [pow_succ, pow_two, pow_succ, pow_two,
      ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_mul]
  rw [← hcoe]
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
  simpa only [ArithmeticFunction.natCoe_apply, Nat.cast_pow,
    Nat.cast_ofNat] using hcast

private theorem shiftedInvNatTwist_zeta_cube_eq (d : ℕ) :
    shiftedInvNatTwist
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      ((shiftedInvNatTwist
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  congr 1
  rw [pow_succ, pow_two, shiftedInvNatTwist_mul,
    shiftedInvNatTwist_mul, pow_succ, pow_two]

private theorem shiftedInvNatTwist_zeta_cube_nonneg (d : ℕ) :
    0 ≤ ((shiftedInvNatTwist
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  change 0 ≤ (z ^ 3) d
  rw [pow_succ, pow_two, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (shiftedInvNatTwist_zeta_nonneg q.1)
      (shiftedInvNatTwist_zeta_nonneg q.2)
  · exact shiftedInvNatTwist_zeta_nonneg p.2

private theorem shiftedLemma6LinearWeight_le_cube (d : ℕ) :
    lemma6LinearWeight d ≤
      ((shiftedInvNatTwist
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    rw [← shiftedInvNatTwist_zeta_cube_eq]
    unfold lemma6LinearWeight distinctPrimeFactors
    rw [shiftedInvNatTwist_apply, if_neg hd0,
      shifted_zeta_cube_apply_squarefree_real hd]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs,
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
      norm_num
    rw [hmu, one_mul]
  · unfold lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
    exact shiftedInvNatTwist_zeta_cube_nonneg d

theorem sum_shiftedSieveModuli_lemma6LinearWeight_le
    (h x : ℕ) (ε : ℝ) :
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d ≤
      (harmonic x : ℝ) ^ 3 := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hsubset : shiftedSieveModuli h x ε ⊆ Finset.Ioc 0 x := by
    intro d hd
    rw [shiftedSieveModuli, Finset.mem_filter] at hd
    rw [Finset.mem_Ioc]
    have hdrange : d < x + 1 := Finset.mem_range.mp hd.1
    exact ⟨by omega, by omega⟩
  calc
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d ≤
        ∑ d ∈ shiftedSieveModuli h x ε, (z ^ 3) d := by
      apply Finset.sum_le_sum
      intro d hd
      exact shiftedLemma6LinearWeight_le_cube d
    _ ≤ ∑ d ∈ Finset.Ioc 0 x, (z ^ 3) d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd hnot
      exact shiftedInvNatTwist_zeta_cube_nonneg d
    _ ≤ (harmonic x : ℝ) ^ 3 :=
      sum_shiftedInvNatTwist_zeta_cube_le x

theorem sum_shiftedSieveModuli_lemma6TotientWeight_le
    {h x : ℕ} (hx2 : 2 ≤ x) (ε : ℝ) :
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
      1 + (2 / Real.log 2) * Real.log x *
        (harmonic x : ℝ) ^ 3 := by
  calc
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
        1 + ∑ d ∈ (shiftedSieveModuli h x ε).erase 1,
          lemma6TotientWeight d := by
      by_cases h1 : 1 ∈ shiftedSieveModuli h x ε
      · rw [← Finset.add_sum_erase _ _ h1]
        simp [lemma6TotientWeight, distinctPrimeFactors]
      · rw [Finset.erase_eq_self.mpr h1]
        linarith
    _ ≤ 1 + ∑ d ∈ (shiftedSieveModuli h x ε).erase 1,
          ((2 / Real.log 2) * Real.log x) * lemma6LinearWeight d := by
      gcongr with d hd
      exact shiftedLemma6TotientWeight_le_log_mul_linearWeight
        (Finset.mem_of_mem_erase hd) (by
          have hdne := Finset.ne_of_mem_erase hd
          have hdpos :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).2.1
          omega)
    _ ≤ 1 + ((2 / Real.log 2) * Real.log x) *
          ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d := by
      rw [Finset.mul_sum]
      apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _)
      intro d hd hnot
      exact mul_nonneg (by
        have hx1 : 1 ≤ x := by omega
        have : (0 : ℝ) ≤ Real.log x :=
          Real.log_nonneg (by exact_mod_cast hx1)
        positivity) (lemma6LinearWeight_nonneg d)
    _ ≤ 1 + (2 / Real.log 2) * Real.log x *
          (harmonic x : ℝ) ^ 3 := by
      gcongr
      exact sum_shiftedSieveModuli_lemma6LinearWeight_le h x ε

theorem shiftedSieveModuli_mem_lemma6MRange
    {h x m : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (hm : m ∈ shiftedSieveModuli h x ε) (hm1 : m ≠ 1) :
    m ∈ lemma6MRange x := by
  rw [mem_lemma6MRange]
  have hmdata := Finset.mem_filter.mp hm
  have hmpos : 1 ≤ m := hmdata.2.1
  have hmx : m ≤ x := by
    have := Finset.mem_range.mp hmdata.1
    omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  refine ⟨by omega, hmx, ?_⟩
  calc
    (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hmdata.2.2.2
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hxR (by linarith)

theorem shiftedLemma6IndependentMajorant_le_nm_bound
    {h x : ℕ} {ε M : ℝ} (hx4 : 4 ≤ x) (hε : 0 ≤ ε)
    (hone : shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2)
    (hM : ∀ m ∈ lemma6MRange x, shiftedLemma6Nm h x ε m ≤ M) :
    shiftedLemma6IndependentMajorant h x ε ≤
      (∑ m ∈ shiftedSieveModuli h x ε, lemma6TotientWeight m) *
        ((2 / Real.log 2) * Real.log x * M) := by
  have hx1 : 1 ≤ x := by omega
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hfactor0 : 0 ≤ (2 / Real.log 2) * Real.log x := by
    positivity
  have hNmAll : ∀ m ∈ shiftedSieveModuli h x ε,
      shiftedLemma6Nm h x ε m ≤ M := by
    intro m hm
    by_cases hm1 : m = 1
    · subst m
      rw [hone]
      exact hM 2 (two_mem_lemma6MRange hx4)
    · exact hM m
        (shiftedSieveModuli_mem_lemma6MRange hx1 hε hm hm1)
  rw [shiftedLemma6IndependentMajorant_eq_bisum]
  calc
    ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          (∑ l ∈ shiftedSieveModuli h x ε,
            if l = 1 then 0
            else lemma6TotientWeight l *
              ‖shiftedLemma6PrimitiveBlock h x m l‖) ≤
      ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ((2 / Real.log 2) * Real.log x *
            shiftedLemma6Nm h x ε m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left shiftedLemma6_inner_sum_le_nm
        (lemma6TotientWeight_nonneg m)
    _ ≤ ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ((2 / Real.log 2) * Real.log x * M) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left (hNmAll m hm) hfactor0
      · exact lemma6TotientWeight_nonneg m
    _ = (∑ m ∈ shiftedSieveModuli h x ε,
          lemma6TotientWeight m) *
        ((2 / Real.log 2) * Real.log x * M) := by
      rw [Finset.sum_mul]

theorem shiftedLemma6NmTerm_le_shiftedLemma6Nm
    {h x l m : ℕ} {ε : ℝ}
    (hl : l ∈ (shiftedSieveModuli h x ε).erase 1) :
    shiftedLemma6NmTerm h x m l ≤ shiftedLemma6Nm h x ε m := by
  unfold shiftedLemma6Nm
  exact Finset.single_le_sum
    (fun l hl => shiftedLemma6NmTerm_nonneg h x m l) hl

theorem exists_shiftedLemma6Nm_max
    {h x : ℕ} (hx : 4 ≤ x) (ε : ℝ) :
    ∃ m ∈ lemma6MRange x, ∀ m' ∈ lemma6MRange x,
      shiftedLemma6Nm h x ε m' ≤ shiftedLemma6Nm h x ε m :=
  Finset.exists_max_image (lemma6MRange x) (shiftedLemma6Nm h x ε)
    (lemma6MRange_nonempty hx)

/-- Shifted equation (12), before choosing the finite maximizing cofactor. -/
theorem shiftedMTwo_le_log6_mul_nm_uniform
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) (_hε' : ε < 1 / 100) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      ∀ M : ℝ,
        (∀ m ∈ lemma6MRange x, shiftedLemma6Nm h x ε m ≤ M) →
          shiftedMTwo h x ε ≤ A * (Real.log x) ^ 6 * M := by
  let c : ℝ := 2 / Real.log 2
  let A : ℝ := c * (1 + 8 * c)
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A, c]
    positivity
  · have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
    have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually hlogOneReal
    filter_upwards [hlogOne, eventually_shiftedLemma6Nm_one_eq_two h ε,
      eventually_ge_atTop 4] with x hxlog hone hx4
    intro M hM
    let L : ℝ := Real.log x
    let H : ℝ := harmonic x
    have hc0 : 0 ≤ c := by
      dsimp only [c]
      positivity
    have hL0 : 0 ≤ L := zero_le_one.trans hxlog
    have hM0 : 0 ≤ M :=
      (shiftedLemma6Nm_nonneg h x ε 2).trans
        (hM 2 (two_mem_lemma6MRange hx4))
    have hH0 : 0 ≤ H := by
      dsimp only [H]
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
      positivity
    have hHle : H ≤ 2 * L := by
      dsimp only [H, L]
      have hH := harmonic_le_one_add_log x
      linarith
    have hL4 : (1 : ℝ) ≤ L ^ 4 := by
      have : (1 : ℝ) ^ 4 ≤ L ^ 4 := by gcongr
      simpa using this
    have houter := sum_shiftedSieveModuli_lemma6TotientWeight_le
      (h := h) (x := x) (by omega : 2 ≤ x) ε
    have houter' :
        ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
          (1 + 8 * c) * L ^ 4 := by
      calc
        ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
            1 + c * L * H ^ 3 := by
          simpa only [c, L, H] using houter
        _ ≤ 1 + c * L * (2 * L) ^ 3 := by gcongr
        _ = 1 + 8 * c * L ^ 4 := by ring
        _ ≤ L ^ 4 + 8 * c * L ^ 4 := add_le_add_left hL4 _
        _ = (1 + 8 * c) * L ^ 4 := by ring
    have hind := shiftedLemma6IndependentMajorant_le_nm_bound
      hx4 hε.le hone hM
    have hfactorM0 : 0 ≤ c * L * M := by positivity
    have hL5le6 : L ^ 5 ≤ L ^ 6 := by
      calc
        L ^ 5 ≤ L ^ 5 * L :=
          le_mul_of_one_le_right (pow_nonneg hL0 5) hxlog
        _ = L ^ 6 := by ring
    calc
      shiftedMTwo h x ε ≤ shiftedLemma6IndependentMajorant h x ε :=
        shiftedMTwo_le_shiftedLemma6IndependentMajorant h x ε
      _ ≤ (∑ d ∈ shiftedSieveModuli h x ε,
            lemma6TotientWeight d) * (c * L * M) := by
        simpa only [c, L] using hind
      _ ≤ ((1 + 8 * c) * L ^ 4) * (c * L * M) :=
        mul_le_mul_of_nonneg_right houter' hfactorM0
      _ = A * L ^ 5 * M := by
        dsimp only [A]
        ring
      _ ≤ A * L ^ 6 * M := by
        gcongr
      _ = A * (Real.log x) ^ 6 * M := by rfl

/-- Shifted equation (12), with its finite maximizing cofactor explicit. -/
theorem shiftedMTwo_le_log6_mul_nm
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      ∃ m : ℕ, 1 < m ∧
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) ∧
        shiftedMTwo h x ε ≤
          A * (Real.log x) ^ 6 * shiftedLemma6Nm h x ε m := by
  obtain ⟨A, hA, huniform⟩ :=
    shiftedMTwo_le_log6_mul_nm_uniform h ε hε hε'
  refine ⟨A, hA, ?_⟩
  filter_upwards [huniform, eventually_ge_atTop 4] with x hxuniform hx4
  obtain ⟨m, hmRange, hmmax⟩ := exists_shiftedLemma6Nm_max
    (h := h) hx4 ε
  have hm := mem_lemma6MRange.mp hmRange
  refine ⟨m, hm.1, hm.2.2, ?_⟩
  exact hxuniform (shiftedLemma6Nm h x ε m) hmmax

/-- The shifted small-conductor part handled by equation (21). -/
noncomputable def shiftedLemma6NmSmall
    (h x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ ((shiftedSieveModuli h x ε).erase 1).filter
      (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100),
    shiftedLemma6NmTerm h x m l

/-- The shifted positive-dyadic-conductor range. -/
noncomputable def shiftedLemma6LargeConductors
    (h x : ℕ) (ε : ℝ) : Finset ℕ :=
  ((shiftedSieveModuli h x ε).erase 1).filter
    (fun l : ℕ => ¬(l : ℝ) ≤ (Real.log x) ^ 100)

noncomputable def shiftedLemma6NmLarge
    (h x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ shiftedLemma6LargeConductors h x ε,
    shiftedLemma6NmTerm h x m l

theorem shiftedLemma6Nm_eq_small_add_large
    (h x : ℕ) (ε : ℝ) (m : ℕ) :
    shiftedLemma6Nm h x ε m =
      shiftedLemma6NmSmall h x ε m +
        shiftedLemma6NmLarge h x ε m := by
  unfold shiftedLemma6Nm shiftedLemma6NmSmall shiftedLemma6NmLarge
    shiftedLemma6LargeConductors
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := (shiftedSieveModuli h x ε).erase 1)
      (p := fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100)
      (f := shiftedLemma6NmTerm h x m)).symm

/-- The shifted finite block has the same equation-(21) character integrals;
only its unit-modulus phase is evaluated at the fixed shift `h`. -/
theorem shiftedLemma6PrimitiveBlock_eq_equation21CharacterIntegral
    {h x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m : ℕ) :
    shiftedLemma6PrimitiveBlock h x m l =
      primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (h : ZMod l)) *
          lemma6Equation21CharacterIntegral x m l χ) := by
  unfold shiftedLemma6PrimitiveBlock
  apply congrArg (primComplexSum l)
  funext χ
  rw [show (chenPairs x).filter (fun q => Nat.Coprime (q.1 * q.2) m) =
      lemma6AdmissiblePairs x m by rfl]
  rw [lemma6_finiteMellin_sum_eq_logDeriv_verticalIntegral
    hx hxlog (lemma6AdmissiblePairs x m)
      (fun q hq => by
        have hqchen : q ∈ chenPairs x := (Finset.mem_filter.mp hq).1
        have hqdata := (Finset.mem_filter.mp hqchen).2
        exact ⟨hqdata.1, hqdata.2.1⟩) χ]
  unfold lemma6Equation21CharacterIntegral
  rw [dif_neg (NeZero.ne l)]

theorem norm_shiftedLemma6PrimitiveBlock_le_mul_of_equation21_character_bound
    {h x l m : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hchar : ∀ χ : DirichletCharacter ℂ l, χ.IsPrimitive →
      ‖lemma6Equation21CharacterIntegral x m l χ‖ ≤ M) :
    ‖shiftedLemma6PrimitiveBlock h x m l‖ ≤ (l : ℝ) * M := by
  rw [shiftedLemma6PrimitiveBlock_eq_equation21CharacterIntegral hx hxlog]
  unfold primComplexSum
  rw [tsum_fintype]
  calc
    ‖∑ χ : DirichletCharacter ℂ l,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (h : ZMod l)) *
            lemma6Equation21CharacterIntegral x m l χ else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ l,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (h : ZMod l)) *
            lemma6Equation21CharacterIntegral x m l χ else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ l, M := by
      apply Finset.sum_le_sum
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul]
        have hstar : ‖starRingEnd ℂ (χ (h : ZMod l))‖ ≤ 1 := by
          simpa using DirichletCharacter.norm_le_one χ (h : ZMod l)
        calc
          ‖starRingEnd ℂ (χ (h : ZMod l))‖ *
              ‖lemma6Equation21CharacterIntegral x m l χ‖ ≤
              1 * M := mul_le_mul hstar
                (hchar χ hp) (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      · simp only [hp, if_false, norm_zero]
        exact hM
    _ = (Fintype.card (DirichletCharacter ℂ l) : ℝ) * M := by simp
    _ = (Nat.totient l : ℝ) * M := by
      rw [Fintype.card_eq_nat_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    _ ≤ (l : ℝ) * M := by
      gcongr
      exact_mod_cast Nat.totient_le l

theorem shiftedLemma6_small_weighted_moduli_le_log103
    {h x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    ∑ l ∈ ((shiftedSieveModuli h x ε).erase 1).filter
        (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100),
        lemma6LinearWeight l * (l : ℝ) ≤
      8 * (Real.log x) ^ 103 := by
  let S := ((shiftedSieveModuli h x ε).erase 1).filter
    (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100)
  let L : ℝ := Real.log (x : ℝ)
  have hL0 : 0 ≤ L := zero_le_one.trans hxlog
  have hH0 : 0 ≤ (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : (harmonic x : ℝ) ≤ 2 * L := by
    have hH := harmonic_le_one_add_log x
    dsimp only [L]
    linarith
  have hSsub : S ⊆ shiftedSieveModuli h x ε := by
    intro l hl
    exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hl).1
  calc
    ∑ l ∈ ((shiftedSieveModuli h x ε).erase 1).filter
        (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100),
        lemma6LinearWeight l * (l : ℝ) =
      ∑ l ∈ S, lemma6LinearWeight l * (l : ℝ) := by rfl
    _ ≤ ∑ l ∈ S, lemma6LinearWeight l * L ^ 100 := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hl).2
        (lemma6LinearWeight_nonneg l)
    _ = L ^ 100 * ∑ l ∈ S, lemma6LinearWeight l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ L ^ 100 *
        ∑ l ∈ shiftedSieveModuli h x ε, lemma6LinearWeight l := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL0 _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun l hl hnot => lemma6LinearWeight_nonneg l)
    _ ≤ L ^ 100 * (harmonic x : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (sum_shiftedSieveModuli_lemma6LinearWeight_le h x ε)
        (pow_nonneg hL0 _)
    _ ≤ L ^ 100 * (2 * L) ^ 3 := by gcongr
    _ = 8 * (Real.log x) ^ 103 := by
      dsimp only [L]
      ring

def ShiftedLemma6Equation21ContourEstimate (h : ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    ∀ m : ℕ, 1 < m →
      (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
      shiftedLemma6NmSmall h x ε m ≤
        C * (Real.log x) ^ 200 * lemma6Equation21PairSum x

theorem shiftedLemma6Equation21ContourEstimate_of_characterBound
    (hchar : Lemma6Equation21CharacterBound) (h : ℕ) (ε : ℝ) :
    ShiftedLemma6Equation21ContourEstimate h ε := by
  obtain ⟨C, hC, hchar⟩ := hchar
  refine ⟨8 * C, by positivity, ?_⟩
  have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hchar, hlogOne, eventually_ge_atTop 2] with
      x hxchar hxlog hx2
  intro m hm1 hmx
  let S := ((shiftedSieveModuli h x ε).erase 1).filter
    (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100)
  let L : ℝ := Real.log (x : ℝ)
  let P : ℝ := lemma6Equation21PairSum x
  let M : ℝ := C * L ^ 90 * P
  have hL0 : 0 ≤ L := zero_le_one.trans hxlog
  have hP0 : 0 ≤ P := lemma6Equation21PairSum_nonneg x
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hterm : ∀ l ∈ S,
      shiftedLemma6NmTerm h x m l ≤
        lemma6LinearWeight l * (l : ℝ) * M := by
    intro l hl
    have hlErase := (Finset.mem_filter.mp hl).1
    have hlSieve : l ∈ shiftedSieveModuli h x ε :=
      Finset.mem_of_mem_erase hlErase
    have hlone : 1 ≤ l := by
      have := (Finset.mem_filter.mp hlSieve).2.1
      omega
    have hlne : l ≠ 1 := Finset.ne_of_mem_erase hlErase
    have hl2 : 2 ≤ l := by omega
    letI : NeZero l := ⟨by omega⟩
    have hnorm : ‖shiftedLemma6PrimitiveBlock h x m l‖ ≤
        (l : ℝ) * M :=
      norm_shiftedLemma6PrimitiveBlock_le_mul_of_equation21_character_bound
        hx2 hxlog hM0 fun χ hχ => by
          exact hxchar m l χ hl2 (Finset.mem_filter.mp hl).2 hχ
    unfold shiftedLemma6NmTerm
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hnorm (lemma6LinearWeight_nonneg l)
  have hsumWeight :=
    shiftedLemma6_small_weighted_moduli_le_log103
      (h := h) (x := x) (ε := ε) hxlog
  calc
    shiftedLemma6NmSmall h x ε m =
        ∑ l ∈ S, shiftedLemma6NmTerm h x m l := by rfl
    _ ≤ ∑ l ∈ S, lemma6LinearWeight l * (l : ℝ) * M := by
      exact Finset.sum_le_sum hterm
    _ = (∑ l ∈ S, lemma6LinearWeight l * (l : ℝ)) * M := by
      rw [Finset.sum_mul]
    _ ≤ (8 * L ^ 103) * M := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [S, L] using hsumWeight) hM0
    _ = 8 * C * L ^ 193 * P := by
      dsimp only [M]
      ring
    _ ≤ 8 * C * L ^ 200 * P := by
      have hpow : L ^ 193 ≤ L ^ 200 :=
        pow_le_pow_right₀ hxlog (by omega)
      gcongr
    _ = (8 * C) * (Real.log x) ^ 200 *
        lemma6Equation21PairSum x := by
      dsimp only [L, P]

theorem shiftedLemma6_nmSmall_le_log18_of_equation21_contour_estimate
    {h : ℕ} {ε : ℝ}
    (hcontour : ShiftedLemma6Equation21ContourEstimate h ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        shiftedLemma6NmSmall h x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 := by
  obtain ⟨C, hC, hcontour⟩ := hcontour
  refine ⟨1, one_pos, ?_⟩
  have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hcontour, hlogOne,
      eventually_const_mul_log220_le_exp_sqrt_log (4 * C)] with
      x hxcontour hxlog habsorb
  intro m hm1 hmx
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := Real.sqrt L
  let η : ℝ := 1 / y
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hxlog
  have hypos : 0 < y := by
    dsimp only [y]
    exact Real.sqrt_pos.2 hLpos
  have hxpos : (0 : ℝ) < x := by
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      norm_num at hxlog
    exact_mod_cast Nat.pos_of_ne_zero hxne
  have hη0 : 0 ≤ η := by dsimp only [η]; positivity
  have hH0 : 0 ≤ (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : (harmonic x : ℝ) ≤ 2 * L := by
    have hH := harmonic_le_one_add_log x
    dsimp only [L]
    linarith
  have hHsq : (harmonic x : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hHle) (add_nonneg hH0 (by positivity : 0 ≤ 2 * L))]
  have hpair := sum_pairQuotient_rpow_le_harmonic x hη0
  have hLy : L = y ^ 2 := by
    dsimp only [y]
    exact (Real.sq_sqrt hLpos.le).symm
  have harg : L * (1 - η / 6) = L - y / 6 := by
    dsimp only [η]
    rw [hLy]
    field_simp
  have hrpow :
      (x : ℝ) ^ (1 - η / 6) =
        (x : ℝ) / Real.exp (y / 6) := by
    rw [Real.rpow_def_of_pos hxpos]
    rw [show Real.log (x : ℝ) = L by rfl, harg, Real.exp_sub,
      show Real.exp L = (x : ℝ) by
        dsimp only [L]
        exact Real.exp_log hxpos]
  have hEpos : 0 < Real.exp (y / 6) := Real.exp_pos _
  have hLpowpos : 0 < L ^ 18 := pow_pos hLpos _
  have habsorb' : 4 * C * L ^ 220 ≤ Real.exp (y / 6) := by
    simpa only [L, y] using habsorb
  have hcoeff :
      4 * C * L ^ 202 / Real.exp (y / 6) ≤ 1 / L ^ 18 := by
    rw [div_le_iff₀ hEpos]
    rw [show 1 / L ^ 18 * Real.exp (y / 6) =
        Real.exp (y / 6) / L ^ 18 by ring]
    rw [le_div_iff₀ hLpowpos]
    calc
      4 * C * L ^ 202 * L ^ 18 = 4 * C * L ^ 220 := by ring
      _ ≤ Real.exp (y / 6) := habsorb'
  calc
    shiftedLemma6NmSmall h x ε m ≤
        C * L ^ 200 * lemma6Equation21PairSum x := by
      simpa only [L] using hxcontour m hm1 hmx
    _ = C * L ^ 200 *
        ∑ q ∈ chenPairs x,
          ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - η) := by
      unfold lemma6Equation21PairSum
      dsimp only [η, y, L]
    _ ≤ C * L ^ 200 *
        ((x : ℝ) ^ (1 - η / 6) * (harmonic x : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    _ ≤ C * L ^ 200 *
        ((x : ℝ) ^ (1 - η / 6) * (4 * L ^ 2)) := by
      gcongr
    _ = 4 * C * L ^ 202 *
        ((x : ℝ) ^ (1 - η / 6)) := by ring
    _ = (x : ℝ) *
        (4 * C * L ^ 202 / Real.exp (y / 6)) := by
      rw [hrpow]
      ring
    _ ≤ (x : ℝ) * (1 / L ^ 18) :=
      mul_le_mul_of_nonneg_left hcoeff hxpos.le
    _ = (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 18 := by
      dsimp only [L]
      ring

theorem shiftedLemma6_equation21_contour_estimate
    (h : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1 / 100) :
    ShiftedLemma6Equation21ContourEstimate h ε :=
  shiftedLemma6Equation21ContourEstimate_of_characterBound
    lemma6_equation21_character_bound h ε

/-- Shifted equation (21): the fixed phase costs no more than one in norm. -/
theorem shiftedLemma6_nmSmall_le_log18
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        shiftedLemma6NmSmall h x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 :=
  shiftedLemma6_nmSmall_le_log18_of_equation21_contour_estimate
    (shiftedLemma6_equation21_contour_estimate h ε hε hε')

noncomputable def shiftedLemma6LargeSquarefreeConductors
    (h x : ℕ) (ε : ℝ) : Finset ℕ :=
  (shiftedLemma6LargeConductors h x ε).filter Squarefree

theorem shiftedLemma6NmLarge_eq_squarefree_sum
    (h x : ℕ) (ε : ℝ) (m : ℕ) :
    shiftedLemma6NmLarge h x ε m =
      ∑ d ∈ shiftedLemma6LargeSquarefreeConductors h x ε,
        shiftedLemma6NmTerm h x m d := by
  unfold shiftedLemma6NmLarge shiftedLemma6LargeSquarefreeConductors
  have hzero :
      ∑ d ∈ (shiftedLemma6LargeConductors h x ε).filter
          (fun d => ¬Squarefree d), shiftedLemma6NmTerm h x m d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdnsq := (Finset.mem_filter.mp hd).2
    unfold shiftedLemma6NmTerm lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdnsq]
    norm_num
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := shiftedLemma6LargeConductors h x ε) (p := Squarefree)
    (f := shiftedLemma6NmTerm h x m)
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

noncomputable def shiftedLemma6LargeBlockIndices
    (h x : ℕ) (ε : ℝ) : Finset ℕ :=
  (shiftedLemma6LargeSquarefreeConductors h x ε).image
    (lemma6ModulusBlockIndex x)

theorem shiftedLemma6LargeSquarefreeConductor_exists_block
    {h x d : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hd : d ∈ shiftedLemma6LargeSquarefreeConductors h x ε) :
    ∃ l : ℕ, 1 ≤ l ∧ d ∈ lemma6ModulusBlock x l := by
  have hddata := hd
  rw [shiftedLemma6LargeSquarefreeConductors, Finset.mem_filter] at hddata
  have hdlarge := hddata.1
  rw [shiftedLemma6LargeConductors, Finset.mem_filter] at hdlarge
  have hdsieve : d ∈ shiftedSieveModuli h x ε :=
    Finset.mem_of_mem_erase hdlarge.1
  have hsievedata := hdsieve
  rw [shiftedSieveModuli, Finset.mem_filter] at hsievedata
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hsievedata.1
    omega
  exact exists_mem_lemma6ModulusBlock hxlog
    (lt_of_not_ge hdlarge.2) hddata.2 hdx

theorem shiftedLemma6LargeConductor_fiber_eq_block
    {h x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    (shiftedLemma6LargeSquarefreeConductors h x ε).filter
        (fun d => lemma6ModulusBlockIndex x d = l) =
      (shiftedLemma6LargeSquarefreeConductors h x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l) := by
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hindex⟩
    obtain ⟨k, hk1, hk⟩ :=
      shiftedLemma6LargeSquarefreeConductor_exists_block hxlog hd
    have hcanonical := lemma6ModulusBlockIndex_mem ⟨k, hk⟩
    rw [hindex] at hcanonical
    exact ⟨hd, hcanonical⟩
  · rintro ⟨hd, hdblock⟩
    exact ⟨hd, lemma6ModulusBlockIndex_eq hdblock⟩

theorem shiftedLemma6NmLarge_eq_sum_blocks
    {h x m : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    shiftedLemma6NmLarge h x ε m =
      ∑ l ∈ shiftedLemma6LargeBlockIndices h x ε,
        ∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
            (fun d => d ∈ lemma6ModulusBlock x l),
          shiftedLemma6NmTerm h x m d := by
  rw [shiftedLemma6NmLarge_eq_squarefree_sum]
  simp_rw [← shiftedLemma6LargeConductor_fiber_eq_block hxlog]
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (shiftedLemma6LargeSquarefreeConductors h x ε)
    (shiftedLemma6LargeBlockIndices h x ε)
    (lemma6ModulusBlockIndex x) (shiftedLemma6NmTerm h x m)
  rw [Finset.filter_eq_self.mpr] at hfiber
  · exact hfiber.symm
  · intro d hd
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

noncomputable def shiftedLemma6NmPairTerm
    (h x m d k : ℕ) : ℝ :=
  lemma6LinearWeight d * ‖shiftedLemma6PrimitivePairBlock h x m d k‖

theorem shiftedLemma6NmPairTerm_nonneg (h x m d k : ℕ) :
    0 ≤ shiftedLemma6NmPairTerm h x m d k := by
  unfold shiftedLemma6NmPairTerm
  exact mul_nonneg (lemma6LinearWeight_nonneg d) (norm_nonneg _)

theorem shifted_sum_largeConductor_pairTerm_le_modulusBlock_sum
    (h x : ℕ) (ε : ℝ) (m l k : ℕ) :
    (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
          (fun d => d ∈ lemma6ModulusBlock x l),
        shiftedLemma6NmPairTerm h x m d k) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        shiftedLemma6NmPairTerm h x m d k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact (Finset.mem_filter.mp hd).2
  · intro d hd hnot
    exact shiftedLemma6NmPairTerm_nonneg h x m d k

theorem shiftedLemma6NmLarge_le_sum_pairBlocks
    {h x m : ℕ} {ε : ℝ} (hx : 1 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) :
    shiftedLemma6NmLarge h x ε m ≤
      ∑ l ∈ shiftedLemma6LargeBlockIndices h x ε,
        ∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
            (fun d => d ∈ lemma6ModulusBlock x l),
          ∑ k ∈ lemma6PairBlockIndices x m,
            shiftedLemma6NmPairTerm h x m d k := by
  rw [shiftedLemma6NmLarge_eq_sum_blocks hxlog]
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro d hd
  unfold shiftedLemma6NmTerm
  rw [shiftedLemma6PrimitiveBlock_eq_sum_pairBlocks hx]
  calc
    lemma6LinearWeight d *
        ‖∑ k ∈ lemma6PairBlockIndices x m,
          shiftedLemma6PrimitivePairBlock h x m d k‖ ≤
      lemma6LinearWeight d *
        ∑ k ∈ lemma6PairBlockIndices x m,
          ‖shiftedLemma6PrimitivePairBlock h x m d k‖ := by
      apply mul_le_mul_of_nonneg_left
      · exact norm_sum_le _ _
      · exact lemma6LinearWeight_nonneg d
    _ = ∑ k ∈ lemma6PairBlockIndices x m,
        shiftedLemma6NmPairTerm h x m d k := by
      unfold shiftedLemma6NmPairTerm
      rw [Finset.mul_sum]

theorem shiftedLemma6LargeBlockIndices_subset_range
    {h x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    shiftedLemma6LargeBlockIndices h x ε ⊆
      Finset.range (Nat.log 2 x + 2) := by
  intro l hl
  rw [shiftedLemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  obtain ⟨k, hk1, hk⟩ :=
    shiftedLemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hcanonical := lemma6ModulusBlockIndex_mem ⟨k, hk⟩
  have hkdata := hcanonical
  rw [lemma6ModulusBlock, Finset.mem_filter] at hkdata
  have hlogpow : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  have hpowltR : ((2 : ℕ) ^ (lemma6ModulusBlockIndex x d - 1) : ℝ) < d := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : ℝ) ^ (lemma6ModulusBlockIndex x d - 1) ≤
          (2 : ℝ) ^ (lemma6ModulusBlockIndex x d - 1) *
            Real.log (x : ℝ) ^ 100 := by
        exact le_mul_of_one_le_right (by positivity) hlogpow
      _ < d := hkdata.2.2.1
  have hpowlt : (2 : ℕ) ^ (lemma6ModulusBlockIndex x d - 1) < d := by
    exact_mod_cast hpowltR
  have hddata := hd
  rw [shiftedLemma6LargeSquarefreeConductors, Finset.mem_filter] at hddata
  have hdlarge := hddata.1
  rw [shiftedLemma6LargeConductors, Finset.mem_filter] at hdlarge
  have hdsieve : d ∈ shiftedSieveModuli h x ε :=
    Finset.mem_of_mem_erase hdlarge.1
  have hsievedata := hdsieve
  rw [shiftedSieveModuli, Finset.mem_filter] at hsievedata
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hsievedata.1
    omega
  have hlogbound : lemma6ModulusBlockIndex x d - 1 ≤ Nat.log 2 x :=
    Nat.le_log_of_pow_le (by norm_num) (hpowlt.le.trans hdx)
  rw [Finset.mem_range]
  omega

theorem card_shiftedLemma6LargeBlockIndices_cast_le_log
    {h x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    ((shiftedLemma6LargeBlockIndices h x ε).card : ℝ) ≤
      (1 / Real.log 2 + 2) * Real.log x := by
  have hcardNat : (shiftedLemma6LargeBlockIndices h x ε).card ≤
      Nat.log 2 x + 2 := by
    calc
      (shiftedLemma6LargeBlockIndices h x ε).card ≤
          (Finset.range (Nat.log 2 x + 2)).card :=
        Finset.card_le_card (shiftedLemma6LargeBlockIndices_subset_range hxlog)
      _ = Nat.log 2 x + 2 := Finset.card_range _
  have hcardR : ((shiftedLemma6LargeBlockIndices h x ε).card : ℝ) ≤
      (Nat.log 2 x : ℝ) + 2 := by exact_mod_cast hcardNat
  have hx1 : 1 ≤ x := by
    by_contra hx
    have : x = 0 := by omega
    subst x
    norm_num at hxlog
  have hnatlog := natLog_two_cast_le hx1
  calc
    ((shiftedLemma6LargeBlockIndices h x ε).card : ℝ) ≤
        (Nat.log 2 x : ℝ) + 2 := hcardR
    _ ≤ Real.log x / Real.log 2 + 2 * Real.log x := by
      exact add_le_add hnatlog (by nlinarith)
    _ = (1 / Real.log 2 + 2) * Real.log x := by ring

theorem shiftedLemma6_one_le_of_mem_largeBlockIndices
    {h x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : l ∈ shiftedLemma6LargeBlockIndices h x ε) : 1 ≤ l := by
  rw [shiftedLemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, hdl⟩ := hl
  obtain ⟨j, hj1, hj⟩ :=
    shiftedLemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j :=
    lemma6ModulusBlockIndex_eq hj
  have hjl : j = l := hindex ▸ hdl
  have hmem : d ∈ lemma6ModulusBlock x l := hjl ▸ hj
  by_contra hlt
  push Not at hlt
  interval_cases l
  rw [lemma6ModulusBlock, Finset.mem_filter] at hmem
  have hdsq : (d : ℝ) ≤ (Real.log (x : ℝ)) ^ 100 := by
    have h2 := hmem.2.2.2
    simpa using h2
  have hdd := hd
  rw [shiftedLemma6LargeSquarefreeConductors, Finset.mem_filter] at hdd
  have hdlarge := hdd.1
  rw [shiftedLemma6LargeConductors, Finset.mem_filter] at hdlarge
  exact hdlarge.2 hdsq

theorem shiftedLemma6_log_pow_hundred_lt_dyadicScale
    {h x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : l ∈ shiftedLemma6LargeBlockIndices h x ε) :
    (Real.log (x : ℝ)) ^ 100 < lemma6DyadicModulusScale x l := by
  rw [shiftedLemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, hdl⟩ := hl
  obtain ⟨j, hj1, hj⟩ :=
    shiftedLemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j :=
    lemma6ModulusBlockIndex_eq hj
  have hjl : j = l := hindex ▸ hdl
  have hmem : d ∈ lemma6ModulusBlock x l := hjl ▸ hj
  rw [lemma6ModulusBlock, Finset.mem_filter] at hmem
  have hdlt : (Real.log (x : ℝ)) ^ 100 < (d : ℝ) := by
    have hdd := hd
    rw [shiftedLemma6LargeSquarefreeConductors, Finset.mem_filter] at hdd
    have hdlarge := hdd.1
    rw [shiftedLemma6LargeConductors, Finset.mem_filter] at hdlarge
    exact lt_of_not_ge hdlarge.2
  exact hdlt.trans_le hmem.2.2.2

theorem shiftedLemma6_fiftyfour_le_dyadicScale
    {h x l : ℕ} {ε : ℝ} (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : l ∈ shiftedLemma6LargeBlockIndices h x ε) :
    54 ≤ lemma6DyadicModulusScale x l := by
  have hscale := shiftedLemma6_log_pow_hundred_lt_dyadicScale
    (h := h) (by linarith) hl
  have h3 : (3 : ℝ) ^ 100 ≤ (Real.log (x : ℝ)) ^ 100 :=
    pow_le_pow_left₀ (by norm_num) hxlog 100
  have h4 : (54 : ℝ) ≤ (3 : ℝ) ^ 100 := by norm_num
  linarith

theorem shiftedLemma6_occupied_modulusScale_lt_two_threshold
    {h x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : l ∈ shiftedLemma6LargeBlockIndices h x ε) :
    lemma6DyadicModulusScale x l <
      2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
  rw [shiftedLemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  obtain ⟨j, hj1, hj⟩ :=
    shiftedLemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j :=
    lemma6ModulusBlockIndex_eq hj
  have hjdata := hj
  rw [lemma6ModulusBlock, Finset.mem_filter] at hjdata
  have hdlarge := (Finset.mem_filter.mp hd).1
  have hderase := (Finset.mem_filter.mp hdlarge).1
  have hdsieve : d ∈ shiftedSieveModuli h x ε :=
    Finset.mem_of_mem_erase hderase
  have hdthreshold : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
    (Finset.mem_filter.mp hdsieve).2.2.2
  rw [hindex]
  unfold lemma6DyadicModulusScale
  have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    calc
      (2 : ℝ) ^ j = 2 ^ ((j - 1) + 1) := by congr 1; omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := by ring
  rw [hpow]
  nlinarith [hjdata.2.2.1]

theorem shifted_sum_largeConductor_pairTerm_le_alpha_beta_integrals
    {h x : ℕ} (hx : 2 ≤ x) (hxlog : 3 ≤ Real.log (x : ℝ))
    (ε : ℝ) (m l k H : ℕ)
    (hintA : Integrable (fun ν : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        lemma6ABlockAtAlpha x m l k H ν))
    (hintB : Integrable (fun ν : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
        lemma6BBlockAtBeta x m l k H ν)) :
    (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l),
      shiftedLemma6NmPairTerm h x m d k) ≤
      (1 / (2 * Real.pi)) *
        (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
            (∫ ν : ℝ,
              ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
                lemma6ABlockAtAlpha x m l k H ν) +
          (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
            (∫ ν : ℝ,
              ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν)) := by
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  apply (shifted_sum_largeConductor_pairTerm_le_modulusBlock_sum
    h x ε m l k).trans
  have hd2 : ∀ d ∈ lemma6ModulusBlock x l, 2 ≤ d := fun d hd =>
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hlog1 hd)).1
  have hper : ∀ d ∈ lemma6ModulusBlock x l,
      lemma6LinearWeight d *
          ‖shiftedLemma6PrimitivePairBlock h x m d k‖ ≤
        (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
    intro d hd
    have hd2d := hd2 d hd
    have hd0 : d ≠ 0 := by omega
    letI : NeZero d := ⟨hd0⟩
    have hnorm := norm_shiftedLemma6PrimitivePairBlock_le_A_alpha_add_B_beta
      (h := h) hd2d hx hxlog m k H
      (fun χ hχ => lemma6BHorizontalEdgesVanish_primitive
        hd2d hx hxlog m k H hχ)
      (fun χ hχ => integrable_lemma6BContourIntegrand_beta
        hd2d hx hxlog m k H hχ)
    have hw0 := lemma6LinearWeight_nonneg d
    have hcongA : (∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν)) =
        ∫ ν : ℝ, lemma6BlockAContourNorm x m k H d ν := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold lemma6BlockAContourNorm
      rw [lemma6RawAModulusTotal_eq x m k H _]
    have hcongB : (∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν)) =
        ∫ ν : ℝ, lemma6BlockBContourNorm x m k H d ν := by
      apply integral_congr_ae
      filter_upwards with ν
      rfl
    rw [hcongA, hcongB] at hnorm
    calc
      lemma6LinearWeight d *
          ‖shiftedLemma6PrimitivePairBlock h x m d k‖ ≤
          lemma6LinearWeight d *
            ((1 / (2 * Real.pi)) *
              ((∫ ν : ℝ, lemma6BlockAContourNorm x m k H d ν) +
                ∫ ν : ℝ, lemma6BlockBContourNorm x m k H d ν)) :=
        mul_le_mul_of_nonneg_left hnorm hw0
      _ = (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
        simp only [MeasureTheory.integral_const_mul]
        ring
  have hintA' : ∀ d ∈ lemma6ModulusBlock x l,
      Integrable (fun ν : ℝ => lemma6LinearWeight d *
        lemma6BlockAContourNorm x m k H d ν) := fun d hd =>
    (integrable_lemma6BlockAContourNorm (hd2 d hd) hx hxlog m k H).const_mul
      (lemma6LinearWeight d)
  have hintB' : ∀ d ∈ lemma6ModulusBlock x l,
      Integrable (fun ν : ℝ => lemma6LinearWeight d *
        lemma6BlockBContourNorm x m k H d ν) := fun d hd =>
    (integrable_lemma6BlockBContourNorm (hd2 d hd) hx hxlog m k H).const_mul
      (lemma6LinearWeight d)
  have hpointA : ∀ ν : ℝ,
      (∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          lemma6BlockAContourNorm x m k H d ν) ≤
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          (4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν) := by
    intro ν
    have hAB : 4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν =
        ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          (4 * Real.log (x : ℝ) ^ 2 *
            lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      unfold lemma6ABlockAtAlpha
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hAB, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : d ≠ 0 := by have := hd2 d hd; omega
    letI : NeZero d := ⟨hd0⟩
    have hraw : lemma6RawAModulusTotal d x m k H (lemma6AlphaPoint x ν) ≤
        4 * Real.log (x : ℝ) ^ 2 *
          lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
      rw [lemma6RawAModulusTotal_eq x m k H _]
      have htotal : lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) =
          lemma6AModulus (d := d) x H (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
        unfold lemma6AModulusTotal
        rw [dif_neg hd0]
      rw [htotal]
      exact lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
        (d := d) (H := H) hx (lemma6AdmissiblePairBlock x m k) ν
    have h1 : lemma6LinearWeight d * lemma6BlockAContourNorm x m k H d ν =
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          (lemma6LinearWeight d *
            lemma6RawAModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      unfold lemma6BlockAContourNorm
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hraw (lemma6LinearWeight_nonneg d))
      (norm_nonneg _)
  have hpointB : ∀ ν : ℝ,
      (∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          lemma6BlockBContourNorm x m k H d ν) =
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
          lemma6BBlockAtBeta x m l k H ν := by
    intro ν
    unfold lemma6BBlockAtBeta
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    unfold lemma6BlockBContourNorm
    ring
  have hKαeq : ∀ ν : ℝ,
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ =
        (Real.exp 1 * (x : ℝ)) *
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ := by
    intro ν
    rw [norm_mul, norm_nat_cpow_lemma6AlphaPoint hx]
  have hKβeq : ∀ ν : ℝ,
      ‖(x : ℂ) ^ lemma6BetaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ =
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ := by
    intro ν
    rw [norm_mul, norm_nat_cpow_lemma6BetaPoint hx]
  have hintAmaj : Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        (4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν)) := by
    apply (hintA.const_mul
      (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)))).congr
    filter_upwards with ν
    rw [hKαeq]
    ring
  have hintBmaj : Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6BetaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
        lemma6BBlockAtBeta x m l k H ν) := by
    apply (hintB.const_mul (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2))).congr
    filter_upwards with ν
    rw [hKβeq]
    ring
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d *
          ‖shiftedLemma6PrimitivePairBlock h x m d k‖) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) :=
      Finset.sum_le_sum fun d hd => hper d hd
    _ = (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
      have hsplit : ∀ d ∈ lemma6ModulusBlock x l,
          (1 / (2 * Real.pi)) *
            ((∫ ν : ℝ, lemma6LinearWeight d *
                lemma6BlockAContourNorm x m k H d ν) +
              ∫ ν : ℝ, lemma6LinearWeight d *
                lemma6BlockBContourNorm x m k H d ν) =
          (1 / (2 * Real.pi)) * (∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            (1 / (2 * Real.pi)) * (∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) :=
        fun d _ => by ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        MeasureTheory.integral_finsetSum _ (fun d hd => hintA' d hd),
        MeasureTheory.integral_finsetSum _ (fun d hd => hintB' d hd)]
      ring
    _ ≤ (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ,
              ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
                (4 * Real.log (x : ℝ) ^ 2 *
                  lemma6ABlockAtAlpha x m l k H ν)) +
            ∫ ν : ℝ,
              ‖(x : ℂ) ^ lemma6BetaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact MeasureTheory.integral_mono
          (MeasureTheory.integrable_finsetSum _ fun d hd => hintA' d hd)
          hintAmaj hpointA
      · exact le_of_eq (integral_congr_ae (ae_of_all _ hpointB))
    _ = (1 / (2 * Real.pi)) *
          (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
              (∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)‖ *
                  lemma6ABlockAtAlpha x m l k H ν) +
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              (∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6BetaPoint x ν)‖ *
                  lemma6BBlockAtBeta x m l k H ν)) := by
      have hfunA : (fun ν : ℝ =>
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
            (4 * Real.log (x : ℝ) ^ 2 *
              lemma6ABlockAtAlpha x m l k H ν)) =
          fun ν : ℝ =>
            (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ))) *
              (‖lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6AlphaPoint x ν)‖ *
                lemma6ABlockAtAlpha x m l k H ν) := by
        funext ν
        rw [hKαeq]
        ring
      have hfunB : (fun ν : ℝ =>
          ‖(x : ℂ) ^ lemma6BetaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
            lemma6BBlockAtBeta x m l k H ν) =
          fun ν : ℝ =>
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              (‖lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν) := by
        funext ν
        rw [hKβeq]
        ring
      have hAint : (∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
            (4 * Real.log (x : ℝ) ^ 2 *
              lemma6ABlockAtAlpha x m l k H ν)) =
        4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
          ∫ ν : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
              lemma6ABlockAtAlpha x m l k H ν := by
        rw [hfunA, MeasureTheory.integral_const_mul]
      have hBint : (∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6BetaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
            lemma6BBlockAtBeta x m l k H ν) =
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          ∫ ν : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
              lemma6BBlockAtBeta x m l k H ν := by
        rw [hfunB, MeasureTheory.integral_const_mul]
      rw [hAint, hBint]

theorem shifted_sum_largeConductor_pairTerm_le_scalar_majorant
    {h x : ℕ} (hx : 2 ≤ x)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ε : ℝ) (m l k H : ℕ)
    {Cpair CremP CremT Cp Cm Cd : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 < CremP) (hCremT : 0 < CremT)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd)
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k)
    (hH2 : 2 ≤ H) (hlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤
      8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
      2 * Real.log (x : ℝ))
    (hsq : ∀ nu : ℝ,
      lemma6ABlockAtAlpha x m l k H nu ^ 2 ≤
        (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x nu))) *
          lemma6RemainderSecondMajorant CremP CremT x l H nu)
    (hpair2 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x nu) i ^ 2) ≤
        Cp * lemma6PairSecondMajorant x l m k (lemma6BetaPoint x nu))
    (hmol4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x nu) i ^ 4) ≤
        Cm * lemma6MollifierFourthMajorant x l H)
    (hder4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x nu) i ^ 4) ≤
        Cd * lemma6DerivativeFourthMajorant x l nu) :
    (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l),
      shiftedLemma6NmPairTerm h x m d k) ≤
      lemma6LargePairBlockMajorant x l k H
        Cpair CremP CremT Cp Cm Cd := by
  have hA := integrable_and_integral_kernelNorm_mul_ABlock_le
    hCpair hCremP hCremT hxlog hl hD4 hY (by omega) hlogH hlogHH hlogQ hsq
  have hB := integrable_and_integral_kernelNorm_mul_BBlock_le
    hCp hCm hCd hxlarge hxlog hl hD4 hY hH2 hpair2 hmol4 hder4
  refine (shifted_sum_largeConductor_pairTerm_le_alpha_beta_integrals
    (h := h) hx hxlog ε m l k H hA.1 hB.1).trans ?_
  unfold lemma6LargePairBlockMajorant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hA.2 (by positivity))
    (mul_le_mul_of_nonneg_left hB.2 (by positivity))

theorem shifted_sum_largeConductor_pairTerm_le_scalar20_majorant
    {h x : ℕ} (hx : 2 ≤ x)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ε : ℝ) (m l k H : ℕ)
    {Cpair CremP CremT Cs Cd Cp C4 : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 < CremP) (hCremT : 0 < CremT)
    (hCs : 0 ≤ Cs) (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hC4 : 0 ≤ C4)
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k)
    (hH2 : 2 ≤ H) (hlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤
      8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
      2 * Real.log (x : ℝ))
    (hsq : ∀ nu : ℝ,
      lemma6ABlockAtAlpha x m l k H nu ^ 2 ≤
        (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x nu))) *
          lemma6RemainderSecondMajorant CremP CremT x l H nu)
    (hmol2 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x nu) i ^ 2) ≤
        Cs * lemma6MollifierSecondMajorant x l H)
    (hder4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x nu) i ^ 4) ≤
        Cd * lemma6DerivativeFourthMajorant x l nu)
    (hpair4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x nu) i ^ 4) ≤
        Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu))
    (hpairMajorant : ∀ nu : ℝ,
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu) ≤
        C4 * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) :
    (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l),
      shiftedLemma6NmPairTerm h x m d k) ≤
      lemma6LargePairBlock20Majorant x l k H
        Cpair CremP CremT Cs Cd Cp C4 := by
  have hA := integrable_and_integral_kernelNorm_mul_ABlock_le
    hCpair hCremP hCremT hxlog hl hD4 hY (by omega) hlogH hlogHH hlogQ hsq
  have hB := integrable_and_integral_kernelNorm_mul_B20Block_le
    hCs hCd hCp hC4 hxlarge hxlog hl hD4 hY hH2
    hmol2 hder4 hpair4 hpairMajorant
  refine (shifted_sum_largeConductor_pairTerm_le_alpha_beta_integrals
    (h := h) hx hxlog ε m l k H hA.1 hB.1).trans ?_
  unfold lemma6LargePairBlock20Majorant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hA.2 (by positivity))
    (mul_le_mul_of_nonneg_left hB.2 (by positivity))

end Chen
