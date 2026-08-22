/-
The Pólya--Vinogradov/partial-summation truncation estimate used in
equation (14).  The Fourier--Gauss estimate in `PolyaVinogradov.lean`
gives a uniform bound for character prefixes; Abel summation then turns
that bound into the required `L`-series tail estimate.
-/
import ChenTheorem.Lemma6.PolyaVinogradov
import Mathlib.NumberTheory.LSeries.SumCoeff

open scoped Classical
open Finset Filter Asymptotics MeasureTheory

namespace Chen

noncomputable def lemma6TailCoeff {q : ℕ} (H : ℕ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n ≤ H then 0 else χ n

theorem lemma6TailCoeff_sum_eq_zero_of_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {H n : ℕ}
    (hn : n ≤ H) :
    ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [lemma6TailCoeff, if_pos]
  exact (mem_Icc.mp hk).2.trans hn

theorem lemma6TailCoeff_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (H n : ℕ) :
    ‖∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) := by
  by_cases hn : n ≤ H
  · rw [lemma6TailCoeff_sum_eq_zero_of_le χ hn, norm_zero]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  · have hHn : H ≤ n := le_of_not_ge hn
    have hsum : ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k =
        ∑ k ∈ Ioc H n, χ k := by
      calc
        ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k =
            ∑ k ∈ Ioc H n, lemma6TailCoeff H χ k := by
          symm
          apply Finset.sum_subset
          · intro k hk
            have hk' := mem_Ioc.mp hk
            exact mem_Icc.mpr ⟨by omega, hk'.2⟩
          · intro k hk hkn
            rw [lemma6TailCoeff, if_pos]
            have hkdata := mem_Icc.mp hk
            by_contra h
            exact hkn (mem_Ioc.mpr ⟨lt_of_not_ge h, hkdata.2⟩)
        _ = ∑ k ∈ Ioc H n, χ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [lemma6TailCoeff, if_neg]
          exact not_le.mpr (mem_Ioc.mp hk).1
    rw [hsum]
    have hunion : Icc 0 n = Icc 0 H ∪ Ioc H n := by
      ext k
      simp only [mem_Icc, mem_union, mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 0 H) (Ioc H n) := by
      rw [Finset.disjoint_left]
      intro k hk₁ hk₂
      simp only [mem_Icc] at hk₁
      simp only [mem_Ioc] at hk₂
      omega
    have hsplit : (∑ k ∈ Icc 0 H, χ k) +
        ∑ k ∈ Ioc H n, χ k = ∑ k ∈ Icc 0 n, χ k := by
      rw [← Finset.sum_union hdisj, ← hunion]
    have hsetH : Icc 0 H = range (H + 1) := by
      ext k
      simp only [mem_Icc, mem_range]
      omega
    have hsetn : Icc 0 n = range (n + 1) := by
      ext k
      simp only [mem_Icc, mem_range]
      omega
    rw [hsetH, hsetn] at hsplit
    have hdiff : ∑ k ∈ Ioc H n, χ k =
        (∑ k ∈ range (n + 1), χ k) -
          ∑ k ∈ range (H + 1), χ k := by
      rw [← hsplit]
      abel
    rw [hdiff]
    calc
      ‖(∑ k ∈ range (n + 1), χ k) -
          ∑ k ∈ range (H + 1), χ k‖ ≤
          ‖∑ k ∈ range (n + 1), χ k‖ +
            ‖∑ k ∈ range (H + 1), χ k‖ := norm_sub_le _ _
      _ ≤ 3 * Real.sqrt q * Real.log (2 * q) +
          3 * Real.sqrt q * Real.log (2 * q) := by
        gcongr
        · exact primitive_character_prefix_sum_norm_le hχ hq (n + 1)
        · exact primitive_character_prefix_sum_norm_le hχ hq (H + 1)
      _ = 6 * Real.sqrt q * Real.log (2 * q) := by ring

theorem lemma6TailCoeff_sum_isBigO
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (H : ℕ) :
    (fun n ↦ ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
  simp only [Real.rpow_zero]
  exact Asymptotics.isBigO_one_nat_atTop_iff.mpr
    ⟨6 * Real.sqrt q * Real.log (2 * q),
      lemma6TailCoeff_sum_norm_le hχ hq H⟩

theorem lemma6TailCoeff_LSeries_eq_tail
    {q H : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    LSeries (lemma6TailCoeff H χ) s = lemma6LSeriesTail H s χ := by
  have hcoeff : ∀ n : ℕ, ‖lemma6TailCoeff H χ n‖ ≤ 1 := by
    intro n
    unfold lemma6TailCoeff
    split
    · simp
    · exact χ.norm_le_one n
  have hMask : LSeriesSummable (lemma6TailCoeff H χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ ↦ hcoeff n) hs
  have hMaskTerms : Summable
      (LSeries.term (lemma6TailCoeff H χ) s) := hMask
  have hsplit := hMaskTerms.sum_add_tsum_subtype_compl (Icc 1 H)
  have hfinite : ∑ n ∈ Icc 1 H,
      LSeries.term (lemma6TailCoeff H χ) s n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [LSeries.term_of_ne_zero (by
      have := (mem_Icc.mp hn).1
      omega)]
    rw [lemma6TailCoeff, if_pos (mem_Icc.mp hn).2, zero_div]
  have htail : (∑' n : {n : ℕ // n ∉ Icc 1 H},
      LSeries.term (lemma6TailCoeff H χ) s n) =
      lemma6LSeriesTail H s χ := by
    unfold lemma6LSeriesTail
    apply tsum_congr
    intro n
    by_cases hn0 : (n : ℕ) = 0
    · simpa only [hn0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        LSeries.term_of_ne_zero hn0]
      rw [lemma6TailCoeff, if_neg]
      intro hnH
      exact n.property (mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnH⟩)
  unfold LSeries
  rw [← hsplit, hfinite, zero_add, htail]

theorem lemma6LSeriesTail_norm_le_of_one_lt_re
    {q H : ℕ} [NeZero q] {s : ℂ}
    (hq : 2 ≤ q) (hH : 1 ≤ H) (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖lemma6LSeriesTail H s χ‖ ≤
      6 * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
  let C : ℝ := 6 * Real.sqrt q * Real.log (2 * q)
  let A : ℝ → ℂ := fun t ↦
    ∑ k ∈ Icc 1 ⌊t⌋₊, lemma6TailCoeff H χ k
  let g : ℝ → ℝ := fun t ↦
    (Set.Ioi (H : ℝ)).indicator (fun u ↦ C * u ^ (-2 : ℝ)) t
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hgreal : Integrable g := by
    dsimp only [g]
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ))
        (c := (H : ℝ)) (by norm_num) hHpos).const_mul C)
  have hg : Integrable g (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hgreal.mono_measure Measure.restrict_le_self
  have hpoint : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖A t * (t : ℂ) ^ (-(s + 1))‖ ≤ g t := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    by_cases htH : (H : ℝ) < t
    · have hgval : g t = C * t ^ (-2 : ℝ) := by
        dsimp only [g]
        rw [Set.indicator_of_mem
          (show t ∈ Set.Ioi (H : ℝ) from htH)]
      rw [hgval]
      have hA : ‖A t‖ ≤ C := by
        exact lemma6TailCoeff_sum_norm_le hχ hq H ⌊t⌋₊
      have htone : (1 : ℝ) ≤ t := ht.le
      have hpow : ‖(t : ℂ) ^ (-(s + 1))‖ ≤
          t ^ (-2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
        have hexp : (-(s + 1)).re = -(s.re + 1) := by simp
        rw [hexp]
        exact Real.rpow_le_rpow_of_exponent_le htone (by linarith)
      rw [norm_mul]
      exact mul_le_mul hA hpow
        (norm_nonneg _) hC
    · have htHle : t ≤ H := le_of_not_gt htH
      have hfloorR : (⌊t⌋₊ : ℝ) ≤ H :=
        (Nat.floor_le htpos.le).trans htHle
      have hfloor : ⌊t⌋₊ ≤ H := by exact_mod_cast hfloorR
      have hAzero : A t = 0 := by
        exact lemma6TailCoeff_sum_eq_zero_of_le χ hfloor
      rw [hAzero, zero_mul, norm_zero]
      have hgzero : g t = 0 := by
        dsimp only [g]
        simp [Set.indicator, htH]
      rw [hgzero]
  have hO := lemma6TailCoeff_sum_isBigO hχ hq H
  have hsum : LSeriesSummable (lemma6TailCoeff H χ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      unfold lemma6TailCoeff
      split
      · simp
      · exact χ.norm_le_one n
    · exact hs
  have hrepr := LSeries_eq_mul_integral (lemma6TailCoeff H χ)
    (r := 0) (s := s) le_rfl (by linarith) hsum hO
  rw [← lemma6TailCoeff_LSeries_eq_tail hs χ, hrepr, norm_mul]
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ),
        A t * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * ∫ t in Set.Ioi (1 : ℝ), g t := by
      gcongr
      exact MeasureTheory.norm_integral_le_of_norm_le hg
        ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hpoint))
    _ = ‖s‖ * (C / H) := by
      congr 1
      rw [show (∫ t in Set.Ioi (1 : ℝ), g t) =
          ∫ t in Set.Ioi (H : ℝ), C * t ^ (-2 : ℝ) by
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        simp only [g, Set.indicator_indicator]
        have hinter : Set.Ioi (1 : ℝ) ∩ Set.Ioi (H : ℝ) =
            Set.Ioi (H : ℝ) := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioi]
          constructor
          · exact fun h ↦ h.2
          · intro ht
            exact ⟨(show (1 : ℝ) ≤ H by exact_mod_cast hH).trans_lt ht, ht⟩
        rw [hinter, MeasureTheory.integral_indicator measurableSet_Ioi]]
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hHpos]
      have hpow : (H : ℝ) ^ ((-2 : ℝ) + 1) = (H : ℝ)⁻¹ := by
        norm_num
        rw [Real.rpow_neg_one]
      rw [hpow]
      field_simp
      ring
    _ = 6 * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
      dsimp only [C]
      ring

theorem lemma6LSeriesTail_eq_zero_of_re_eq_one
    {q H : ℕ} [NeZero q] {s : ℂ} (hs : s.re = 1)
    (χ : DirichletCharacter ℂ q) :
    lemma6LSeriesTail H s χ = 0 := by
  have hfull : ¬Summable
      (LSeries.term (fun n : ℕ ↦ χ n) s) := by
    intro h
    have hL : LSeriesSummable (fun n : ℕ ↦ χ n) s := h
    rw [DirichletCharacter.LSeriesSummable_iff
      (s := s) (NeZero.ne q) χ] at hL
    linarith
  have htail : ¬Summable (fun n : {n : ℕ // n ∉ Icc 1 H} ↦
      LSeries.term (fun n : ℕ ↦ χ n) s n) := by
    intro ht
    apply hfull
    let S : Set ℕ := {n : ℕ | n ∉ Icc 1 H}
    have hmasked : Summable (S.indicator
        (LSeries.term (fun n : ℕ ↦ χ n) s)) :=
      (summable_subtype_iff_indicator (s := S)).mp ht
    apply Summable.congr_atTop hmasked
    filter_upwards [eventually_ge_atTop (H + 1)] with n hn
    rw [Set.indicator_of_mem]
    dsimp only [S]
    simp only [Set.mem_setOf_eq]
    intro hmem
    have hnH := (mem_Icc.mp hmem).2
    omega
  unfold lemma6LSeriesTail
  exact tsum_eq_zero_of_not_summable htail

theorem lemma6LFunctionTruncation : Lemma6LFunctionTruncation := by
  refine ⟨6, by norm_num, ?_⟩
  intro q H hqInst s hq hH hs χ hχ
  obtain hsEq | hsLt := hs.eq_or_lt
  · have hzero := lemma6LSeriesTail_eq_zero_of_re_eq_one
      (H := H) hsEq.symm χ
    rw [hzero, norm_zero]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  · exact lemma6LSeriesTail_norm_le_of_one_lt_re hq hH hsLt χ hχ

end Chen
