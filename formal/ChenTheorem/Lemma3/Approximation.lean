/-
Pólya--Vinogradov/Abel truncation for Chen's Lemma 3.

Unlike the absolutely-convergent tail used in equation (14), this module
works on `Re s > 0`.  The analytically continued `LFunction` is first
identified with its Mellin partial-summation integral (proved in
`StripGrowth.lean`), and finite Abel summation then separates a Dirichlet
polynomial from the genuine integral tail.
-/
import ChenTheorem.Lemma3.Polynomial
import ChenTheorem.Lemma6.StripGrowth
import Mathlib.NumberTheory.AbelSummation

open Real Set MeasureTheory Filter Complex
open scoped Classical

namespace Chen

private theorem lemma3_character_zero {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) : χ (0 : ℕ) = 0 := by
  have hI : Fact (1 < q) := ⟨by omega⟩
  exact MulChar.map_nonunit χ (by
    rw [Nat.cast_zero]
    exact not_isUnit_zero)

/-- The Mellin integrand for a primitive character is integrable on every
right half-line when `Re s > 0`. -/
theorem integrableOn_lemma3_mellin {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  have hmajor : IntegrableOn (fun t : ℝ => B * t ^ (-(s.re + 1)))
      (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul B
  apply hmajor.mono'
  · exact (measurable_charPartialSumStep χ).aestronglyMeasurable.mul
      ((continuousOn_cpow_neg_succ_of_one_lt s).aestronglyMeasurable
        measurableSet_Ioi)
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
    change ‖charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      B * t ^ (-(s.re + 1))
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    exact mul_le_mul hstep le_rfl (Real.rpow_nonneg ht0.le _) hB0

/-- Norm bound for the Mellin tail. -/
theorem norm_lemma3_mellin_tail_le {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (N : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) *
        ((N : ℝ) ^ (-s.re) / s.re) := by
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsub : Set.Ioi (N : ℝ) ⊆ Set.Ioi 1 :=
    Set.Ioi_subset_Ioi (by exact_mod_cast hN)
  have hint : IntegrableOn (fun t : ℝ =>
      charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_lemma3_mellin hχ hq hs).mono_set hsub
  have hmajor : IntegrableOn (fun t : ℝ => B * t ^ (-(s.re + 1)))
      (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : -(s.re + 1) < -1) hNpos).const_mul B
  have hpoint : ∀ t ∈ Set.Ioi (N : ℝ),
      ‖charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
        B * t ^ (-(s.re + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := hNpos.trans ht
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    exact mul_le_mul hstep le_rfl (Real.rpow_nonneg ht0.le _) hB0
  calc
    ‖∫ t in Set.Ioi (N : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (N : ℝ), B * t ^ (-(s.re + 1)) := by
        exact norm_integral_le_of_norm_le hmajor
          ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall hpoint))
    _ = B * ((N : ℝ) ^ (-s.re) / s.re) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) hNpos]
      have hs0 : s.re ≠ 0 := ne_of_gt hs
      have hpow : (N : ℝ) ^ (-(s.re + 1) + 1) =
          (N : ℝ) ^ (-s.re) := by congr 1; ring
      rw [hpow]
      congr 1
      field_simp [hs0]
      ring
    _ = 3 * Real.sqrt q * Real.log (2 * q) *
        ((N : ℝ) ^ (-s.re) / s.re) := by rfl

/-- Finite Abel summation, in a raw form that keeps the derivative of
`t ↦ t^(-s)` visible. -/
theorem lemma3TruncatedL_eq_abel {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re)
    (χ : DirichletCharacter ℂ q) :
    lemma3TruncatedL N s χ =
      ((N : ℂ) ^ (-s)) * charPartialSumStep χ N -
        ∫ t in Set.Ioc (1 : ℝ) N,
          deriv (fun u : ℝ => (u : ℂ) ^ (-s)) t *
            charPartialSumStep χ t := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hneg : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N,
      DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    exact differentiableAt_id.ofReal_cpow_const ht0 hneg
  have hintIoi : IntegrableOn
      (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Ioi 1) :=
    integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by simpa using hs)
  have hint : IntegrableOn
      (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc 1 N) :=
    ((Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hintIoi).mono_set
      Set.Icc_subset_Ici_self)
  have hzero := lemma3_character_zero hq χ
  have habel := sum_mul_eq_sub_integral_mul₀'
    (f := fun u : ℝ => (u : ℂ) ^ (-s))
    (c := fun n : ℕ => χ n) hzero N hdiff hint
  have hsum (m : ℕ) :
      ∑ k ∈ Finset.Icc 0 m, χ k = charPartialSumStep χ m := by
    unfold charPartialSumStep
    rw [show Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp), hzero, zero_add]
    simp
  have hleft :
      (∑ k ∈ Finset.Icc 0 N, ((k : ℝ) : ℂ) ^ (-s) * χ k) =
        lemma3TruncatedL N s χ := by
    rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp), hzero, mul_zero, zero_add]
    unfold lemma3TruncatedL lemma3Phase
    apply Finset.sum_congr rfl
    intro n hn
    rw [Complex.cpow_neg, Complex.ofReal_natCast]
  rw [hleft, hsum] at habel
  have hintegral :
      (∫ t in Set.Ioc (1 : ℝ) N,
          deriv (fun u : ℝ => (u : ℂ) ^ (-s)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ k) =
        ∫ t in Set.Ioc (1 : ℝ) N,
          deriv (fun u : ℝ => (u : ℂ) ^ (-s)) t *
            charPartialSumStep χ t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    congr 1
    unfold charPartialSumStep
    rw [show Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp), hzero, zero_add]
  rw [hintegral] at habel
  exact habel

/-- Finite Abel summation in the usual form. -/
theorem lemma3TruncatedL_eq_boundary_add_integral {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re)
    (χ : DirichletCharacter ℂ q) :
    lemma3TruncatedL N s χ =
      ((N : ℂ) ^ (-s)) * charPartialSumStep χ N +
        s * ∫ t in Set.Ioc (1 : ℝ) N,
          charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) := by
  rw [lemma3TruncatedL_eq_abel hq hN hs χ]
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hintegral :
      (∫ t in Set.Ioc (1 : ℝ) N,
          deriv (fun u : ℝ => (u : ℂ) ^ (-s)) t *
            charPartialSumStep χ t) =
        -s * ∫ t in Set.Ioc (1 : ℝ) N,
          charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht.1)
    dsimp only
    rw [Complex.deriv_ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)]
    have hexp : -s - 1 = -(s + 1) := by ring
    rw [hexp]
    ring
  rw [hintegral]
  ring

/-- Exact truncation formula on `Re s > 0`.  This is the conditionally
convergent Dirichlet-series bridge missing from the printed proof. -/
theorem LFunction_sub_lemma3TruncatedL_eq {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s - lemma3TruncatedL N s χ =
      s * (∫ t in Set.Ioi (N : ℝ),
          charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))) -
        ((N : ℂ) ^ (-s)) * charPartialSumStep χ N := by
  let f : ℝ → ℂ := fun t =>
    charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfull : IntegrableOn f (Set.Ioi 1) :=
    integrableOn_lemma3_mellin hχ hq hs
  have htail : IntegrableOn f (Set.Ioi (N : ℝ)) :=
    hfull.mono_set (Set.Ioi_subset_Ioi hNreal)
  have hsplit :
      (∫ t in Set.Ioi (1 : ℝ), f t) =
        (∫ t in Set.Ioc (1 : ℝ) N, f t) +
          ∫ t in Set.Ioi (N : ℝ), f t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hNreal,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hfull.mono_set Set.Ioc_subset_Ioi_self
    · exact htail
  rw [LFunction_eq_mellin_integral hχ hq hs,
    lemma3TruncatedL_eq_boundary_add_integral hq hN hs χ]
  change s * (∫ t in Set.Ioi (1 : ℝ), f t) -
      (((N : ℂ) ^ (-s)) * charPartialSumStep χ N +
        s * ∫ t in Set.Ioc (1 : ℝ) N, f t) = _
  rw [hsplit]
  ring

/-- Uniform Pólya--Vinogradov truncation error on the half-plane used by
Lemma 3. -/
theorem norm_LFunction_sub_lemma3TruncatedL_le {q N : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (hN : 1 ≤ N) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s - lemma3TruncatedL N s χ‖ ≤
      12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) *
        (N : ℝ) ^ (-s.re) := by
  have hspos : 0 < s.re := (by linarith : (0 : ℝ) < s.re)
  have hNpos : 0 < N := by omega
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  let R : ℂ := ∫ t in Set.Ioi (N : ℝ),
    charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))
  let P : ℝ := B * (N : ℝ) ^ (-s.re)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  have hpow0 : 0 ≤ (N : ℝ) ^ (-s.re) := by positivity
  have hP0 : 0 ≤ P := mul_nonneg hB0 hpow0
  have htail : ‖R‖ ≤ P / s.re := by
    dsimp only [R, P, B]
    simpa [mul_div_assoc] using
      norm_lemma3_mellin_tail_le hχ hq hN hspos
  have hstep : ‖charPartialSumStep χ (N : ℝ)‖ ≤ B := by
    dsimp only [B, charPartialSumStep]
    simpa using primitive_char_sum_Icc_norm_le hχ hq N
  have hcpow : ‖((N : ℂ) ^ (-s))‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    simp
  have hsle : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hnormhalf : (1 / 2 : ℝ) ≤ ‖s‖ := hs.trans hsle
  have hratio : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ hspos).2
    nlinarith [norm_nonneg s]
  have hone : (1 : ℝ) ≤ 2 * ‖s‖ := by linarith
  rw [LFunction_sub_lemma3TruncatedL_eq hχ hq hN hspos]
  change ‖s * R - ((N : ℂ) ^ (-s)) * charPartialSumStep χ N‖ ≤ _
  calc
    ‖s * R - ((N : ℂ) ^ (-s)) * charPartialSumStep χ N‖ ≤
        ‖s * R‖ + ‖((N : ℂ) ^ (-s)) * charPartialSumStep χ N‖ :=
      norm_sub_le _ _
    _ = ‖s‖ * ‖R‖ +
        ‖((N : ℂ) ^ (-s))‖ * ‖charPartialSumStep χ N‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ * (P / s.re) + (N : ℝ) ^ (-s.re) * B := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left htail (norm_nonneg s)
      · rw [hcpow]
        exact mul_le_mul_of_nonneg_left hstep hpow0
    _ = (‖s‖ / s.re) * P + P := by
      dsimp only [P]
      field_simp [ne_of_gt hspos]
    _ ≤ (2 * ‖s‖) * P + (2 * ‖s‖) * P := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hratio hP0)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hP0)
    _ = 12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) *
        (N : ℝ) ^ (-s.re) := by
      dsimp only [P, B]
      ring

end Chen
