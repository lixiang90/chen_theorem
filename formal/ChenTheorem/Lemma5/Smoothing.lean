import ChenTheorem.Lemma5.Arithmetic

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! ### Formula (5): smoothing and the square-sieve expansion -/

/-- The first term on the right of formula (5), before the roughness
indicator is replaced by the square of the Selberg divisor sum. -/
noncomputable def smoothedRoughM (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ sieveMIndices x q,
        ArithmeticFunction.vonMangoldt n *
          chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))

/-- The exact loss incurred when inserting Chen's smoothing function into
`M`.  Keeping it as a positive finite sum makes the analytic content of
formula (5) explicit. -/
noncomputable def sieveMSmoothingError (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ sieveMIndices x q,
        ArithmeticFunction.vonMangoldt n *
          (1 - chenPhi x
            ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)))

/-- Inserting `Φ` is an exact decomposition of `M` into its smoothed part
and the smoothing loss. -/
theorem sieveM_eq_smoothedRoughM_add_smoothingError (x : ℕ) :
    sieveM x = smoothedRoughM x + sieveMSmoothingError x := by
  unfold sieveM smoothedRoughM sieveMSmoothingError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The smoothing loss is nonnegative once the pair logarithms are
positive and Lemma 1 supplies `Φ ≤ 1`. -/
theorem sieveMSmoothingError_nonneg
    {x : ℕ} (hx : 1 < x) :
    0 ≤ sieveMSmoothingError x := by
  unfold sieveMSmoothingError
  apply Finset.sum_nonneg
  intro q hq
  have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    one_lt_pairQuotient hq
  have hlog : 0 < Real.log
      ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
    Real.log_pos hY
  apply mul_nonneg (inv_nonneg.mpr hlog.le)
  apply Finset.sum_nonneg
  intro n hn
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr (chenPhi_le_one x
      (by exact_mod_cast hx) hy))

/-- The thin upper-end interval in which Lemma 1 does not yet give
`1 - Φ ≤ x⁻⁰·¹`. -/
noncomputable def smoothingBoundaryIndices
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (sieveMIndices x q).filter fun n =>
    (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))

/-- Weighted rough mass in the transition interval of the smoothing
kernel. -/
noncomputable def smoothingBoundaryMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ smoothingBoundaryIndices x q,
        ArithmeticFunction.vonMangoldt n

/-- Transition mass whose von Mangoldt index has small base prime. -/
noncomputable def smoothingBoundarySmallBaseMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (smoothingBoundaryIndices x q).filter fun n =>
          (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

/-- Transition mass with base prime larger than `x^(1/100)`.  This is the
part to which the two-dimensional upper-bound sieve is applied. -/
noncomputable def smoothingBoundaryLargeBaseMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (smoothingBoundaryIndices x q).filter fun n =>
          ¬(n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

/-- Exact small/large-base partition of the transition mass. -/
theorem smoothingBoundaryMass_eq_small_add_large (x : ℕ) :
    smoothingBoundaryMass x =
      smoothingBoundarySmallBaseMass x +
        smoothingBoundaryLargeBaseMass x := by
  unfold smoothingBoundaryMass smoothingBoundarySmallBaseMass
    smoothingBoundaryLargeBaseMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  congr 1
  simpa only using (Finset.sum_filter_add_sum_filter_not
    (s := smoothingBoundaryIndices x q)
    (p := fun n =>
      (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100))
    (f := fun n => ArithmeticFunction.vonMangoldt n)).symm

/-- Lemma 1 splits the smoothing loss into a global `x⁻⁰·¹ M` term and
the genuinely short transition interval. -/
theorem sieveMSmoothingError_le_interior_add_boundary
    {x : ℕ} (hx1 : 1 < x)
    (hxlog : (10 : ℝ) ^ 4 ≤ Real.log x) :
    sieveMSmoothingError x ≤
      (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x +
        smoothingBoundaryMass x := by
  unfold sieveMSmoothingError sieveM smoothingBoundaryMass
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x
                ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))) ≤
      ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ((x : ℝ) ^ (-(0.1 : ℝ)) *
              ∑ n ∈ sieveMIndices x q,
                ArithmeticFunction.vonMangoldt n +
            ∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro q hq
      have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
        one_lt_pairQuotient hq
      have hlogY : 0 < Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
        Real.log_pos hY
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlogY.le)
      rw [Finset.mul_sum]
      rw [show
          (∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n) =
            ∑ n ∈ sieveMIndices x q,
              if (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
                  Real.exp
                    (2 * (Real.log x) ^ (-(0.1 : ℝ)))
              then ArithmeticFunction.vonMangoldt n
              else 0 by
        unfold smoothingBoundaryIndices
        rw [Finset.sum_filter]]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro n hn
      let y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2 * n)
      have hy0 : 0 ≤ y := by
        dsimp only [y]
        positivity
      have hphi0 : 0 ≤ chenPhi x y :=
        chenPhi_nonneg x (by exact_mod_cast hx1) hy0
      by_cases hboundary :
          y < Real.exp
            (2 * (Real.log x) ^ (-(0.1 : ℝ)))
      · rw [if_pos hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n +
            ArithmeticFunction.vonMangoldt n
        have hloss : 1 - chenPhi x y ≤ 1 := by linarith
        calc
          ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x y) ≤
            ArithmeticFunction.vonMangoldt n * 1 :=
              mul_le_mul_of_nonneg_left hloss
                ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                ArithmeticFunction.vonMangoldt n +
              ArithmeticFunction.vonMangoldt n := by
            have hnonneg :
                0 ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt n :=
              mul_nonneg (Real.rpow_nonneg (by positivity) _)
                ArithmeticFunction.vonMangoldt_nonneg
            linarith
      · rw [if_neg hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n + 0
        have hylarge :
            Real.exp
                (2 * (Real.log x) ^ (-(0.1 : ℝ))) ≤ y :=
          le_of_not_gt hboundary
        have hphi :=
          chenPhi_ge (x := (x : ℝ)) (y := y)
            (by exact_mod_cast hx1) hxlog hylarge
        have hloss :
            1 - chenPhi x y ≤
              (x : ℝ) ^ (-(0.1 : ℝ)) := by
          linarith
        simpa only [add_zero, mul_comm] using
          mul_le_mul_of_nonneg_left hloss
            ArithmeticFunction.vonMangoldt_nonneg
    _ = (x : ℝ) ^ (-(0.1 : ℝ)) *
          ∑ q ∈ chenPairs x,
            (Real.log
              ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
              ∑ n ∈ sieveMIndices x q,
                ArithmeticFunction.vonMangoldt n +
        ∑ q ∈ chenPairs x,
          (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
            ∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- A deliberately crude bound for `M`; after multiplication by
`x⁻⁰·¹` it is already a fixed power saving. -/
theorem sieveM_le_crude
    {x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    sieveM x ≤
      ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
        18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
          Real.log x := by
  unfold sieveM
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
      rpow_third_lt_pairQuotient hq
    have hlogY : (1 : ℝ) ≤ Real.log Y := by
      have hlogpow :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) =
            (1 : ℝ) / 3 * Real.log x := by
        rw [Real.log_rpow hxpos]
      have hpowpos :
          0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hmono :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinvnonneg : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    have hsubset :
        sieveMIndices x q ⊆ smoothedMIndices x q := by
      intro n hn
      have hn' := hn
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hrough :
        ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
          ∑ n ∈ smoothedMIndices x q,
            ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ =>
          ArithmeticFunction.vonMangoldt_nonneg)
    have hmass :
        ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
          (Y + 2) * Real.log x :=
      hrough.trans (by
        simpa only [Y] using
          sum_smoothedMIndices_vonMangoldt_le hx2 q)
    have hmass0 :
        0 ≤ ∑ n ∈ sieveMIndices x q,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    calc
      (Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n =
        (Real.log Y)⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n := by rfl
      _ ≤ 1 * ((Y + 2) * Real.log x) :=
        mul_le_mul hinvle hmass hmass0 (by norm_num)
      _ = ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x := by simp only [Y, one_mul]
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
      apply Finset.sum_le_sum
      exact hpair
    _ = (∑ q ∈ chenPairs x,
          ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2)) *
        Real.log x := by rw [Finset.sum_mul]
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          2 * ((chenPairs x).card : ℝ)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hYsum :
          ∑ q ∈ chenPairs x,
              (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
            (x : ℝ) * (harmonic x : ℝ) ^ 2 := by
        simpa only [sub_zero, zero_div, Real.rpow_one] using
        (sum_pairQuotient_rpow_le_harmonic
          x (ε := 0) (by norm_num))
      calc
        (∑ q ∈ chenPairs x,
            (x : ℝ) / ((q.1 : ℝ) * q.2)) +
              ((chenPairs x).card : ℝ) * 2 =
            2 * ((chenPairs x).card : ℝ) +
              ∑ q ∈ chenPairs x,
                (x : ℝ) / ((q.1 : ℝ) * q.2) := by ring
        _ ≤ 2 * ((chenPairs x).card : ℝ) +
              (x : ℝ) * (harmonic x : ℝ) ^ 2 :=
          add_le_add_right hYsum _
        _ = (x : ℝ) * (harmonic x : ℝ) ^ 2 +
              2 * ((chenPairs x).card : ℝ) := by ring
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard := chenPairs_card_cast_le x
        (show 1 ≤ x by omega)
      have hcard' :
          2 * ((chenPairs x).card : ℝ) ≤
            18 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
        nlinarith
      simpa [add_comm] using
        add_le_add_left hcard'
          ((x : ℝ) * (harmonic x : ℝ) ^ 2)

/-- If the base prime of a prime power is at most `z`, its von Mangoldt
weight is controlled by `z · Λ(n)/minFac(n)`. -/
theorem vonMangoldt_le_rpow_mul_div_minFac
    {x n : ℕ}
    (hsmall :
      (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    ArithmeticFunction.vonMangoldt n ≤
      (x : ℝ) ^ ((1 : ℝ) / 100) *
        (ArithmeticFunction.vonMangoldt n *
          (n.minFac : ℝ)⁻¹) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hn1 : n ≠ 1 := by
      intro hn
      subst n
      simp at hΛ
    have hp : n.minFac.Prime := Nat.minFac_prime hn1
    have hp0 : (n.minFac : ℝ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    have hterm :
        0 ≤ ArithmeticFunction.vonMangoldt n *
          (n.minFac : ℝ)⁻¹ :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (inv_nonneg.mpr (by positivity))
    calc
      ArithmeticFunction.vonMangoldt n =
          (n.minFac : ℝ) *
            (ArithmeticFunction.vonMangoldt n *
              (n.minFac : ℝ)⁻¹) := by
        field_simp
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) *
          (ArithmeticFunction.vonMangoldt n *
            (n.minFac : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hsmall hterm

/-- The small-base-prime part of the smoothing transition is already a
fixed power saving. -/
theorem smoothingBoundarySmallBaseMass_le_explicit
    {x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    smoothingBoundarySmallBaseMass x ≤
      9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
  unfold smoothingBoundarySmallBaseMass
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hH : 0 ≤ (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity) (by linarith)) hH
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
      rpow_third_lt_pairQuotient hq
    have hlogY : (1 : ℝ) ≤ Real.log Y := by
      have hlogpow :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) =
            (1 : ℝ) / 3 * Real.log x := by
        rw [Real.log_rpow hxpos]
      have hpowpos :
          0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hmono :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinv0 : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    let S : Finset ℕ :=
      (smoothingBoundaryIndices x q).filter
        (fun n => (n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
    have hSsubset : S ⊆ smoothedMIndices x q := by
      intro n hn
      have hnBoundary :=
        (Finset.mem_filter.mp hn).1
      have hnSieve :=
        (Finset.mem_filter.mp hnBoundary).1
      have hn' := hnSieve
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hsum :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
      calc
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
            ∑ n ∈ S,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro n hn
          exact vonMangoldt_le_rpow_mul_div_minFac
            (Finset.mem_filter.mp hn).2
        _ ≤ ∑ n ∈ smoothedMIndices x q,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
          intro n hn _
          exact mul_nonneg
            (Real.rpow_nonneg hxpos.le _)
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (inv_nonneg.mpr (by positivity)))
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    have hsumB :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B :=
      hsum.trans (mul_le_mul_of_nonneg_left
        (by simpa only [B] using
          (sum_smoothedMIndices_vonMangoldt_div_minFac_le
            hx2 q))
        (Real.rpow_nonneg hxpos.le _))
    have hsum0 :
        0 ≤ ∑ n ∈ S,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    have hmul :
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      calc
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          1 * ∑ n ∈ S,
            ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_right hinvle hsum0
        _ ≤ 1 * ((x : ℝ) ^ ((1 : ℝ) / 100) * B) :=
          mul_le_mul_of_nonneg_left hsumB (by norm_num)
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) * B := one_mul _
    simpa only [Y, S] using hmul
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      apply Finset.sum_le_sum
      exact hpair
    _ = ((chenPairs x).card : ℝ) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      exact mul_le_mul_of_nonneg_right
        (chenPairs_card_cast_le x (show 1 ≤ x by omega))
        (mul_nonneg (Real.rpow_nonneg hxpos.le _) hB0)
    _ = 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
      have hexp :
          (253 : ℝ) / 300 =
            (5 : ℝ) / 6 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [B]
      ring

/-- The small-base-prime transition mass is negligible in the logarithmic
error scale of Lemma 5. -/
theorem eventually_smoothingBoundarySmallBaseMass_le :
    ∀ᶠ x : ℕ in atTop,
      smoothingBoundarySmallBaseMass x ≤
        (18 * ((Real.log 2)⁻¹ + 1)) *
          (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ))
        (by norm_num)] with
      x hlogFive hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  let L : ℝ := Real.log x
  let H : ℝ := harmonic x
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    linarith
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : H ≤ 2 * L := by
    dsimp only [H, L]
    have hH := harmonic_le_one_add_log x
    linarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hceil :
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ K * L := by
    have hy0 : 0 ≤ L / Real.log 2 := by positivity
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ L / Real.log 2 + 1 :=
        (Nat.ceil_lt_add_one hy0).le
      _ = (Real.log 2)⁻¹ * L + 1 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (Real.log 2)⁻¹ * L + L := by
        linarith
      _ = K * L := by
        dsimp only [K]
        ring
  have hlogs :
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
        2 * K * L ^ 5 := by
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
          (K * L) * L * (2 * L) := by gcongr
      _ = 2 * K * L ^ 3 := by ring
      _ ≤ 2 * K * L ^ 5 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (show 1 ≤ L by
            simpa only [L] using hlogOne) (by norm_num))
          (mul_nonneg (by norm_num) hK0)
  have hexplicit :=
    smoothingBoundarySmallBaseMass_le_explicit hx2 hxlarge
  calc
    smoothingBoundarySmallBaseMass x ≤
        9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          ((⌈L / Real.log 2⌉₊ : ℝ) * L * H) := by
      simpa only [L, H, mul_assoc] using hexplicit
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * L ^ 5) := by
      gcongr
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      dsimp only [L] at hlogFive ⊢
      gcongr
    _ = (18 * K) * (x : ℝ) ^ ((64 : ℝ) / 75) := by
      have hexp :
          (64 : ℝ) / 75 =
            (253 : ℝ) / 300 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring
    _ ≤ (18 * K) * (x : ℝ) ^ (1 - (1 : ℝ) / 10) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
      · exact mul_nonneg (by norm_num) hK0
    _ ≤ (18 * K) *
        ((x : ℝ) / (Real.log x) ^ (2.01 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (by norm_num) hK0)
    _ = (18 * ((Real.log 2)⁻¹ + 1)) *
        (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [K]
      ring

/-- The global `x⁻⁰·¹ M` part of the smoothing loss is negligible compared
with `x / (log x)^2.01`. -/
theorem eventually_smoothingInterior_le :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x ≤
        19 * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  have hδ01 : (0 : ℝ) < 1 / 100 := by norm_num
  have hδ08 : (0 : ℝ) < 8 / 100 := by norm_num
  filter_upwards [eventually_harmonic_sq_le_rpow hδ01,
    eventually_log_pow_four_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (8 : ℝ) / 100) (r := (2.01 : ℝ)) hδ08] with
      x hH hlogFour hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  have hpow01one :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hxone (by norm_num)
  have hlog :
      Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      Real.log x ≤ (Real.log x) ^ 4 := by
        nlinarith [sq_nonneg (Real.log x),
          sq_nonneg ((Real.log x) ^ 2 - Real.log x)]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := hlogFour
  have h56 :
      (x : ℝ) ^ ((5 : ℝ) / 6) ≤ (x : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)).trans_eq
      (Real.rpow_one x)
  have hM := sieveM_le_crude hx2 hxlarge
  have hxx :
      (x : ℝ) ≤ (x : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 100) :=
    le_mul_of_one_le_right hxpos.le hpow01one
  have hinside :
      (x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6) ≤
        (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
          18 * ((x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hH hxpos.le)
      (mul_le_mul_of_nonneg_left (h56.trans hxx) (by norm_num))
  have hM' :
      sieveM x ≤
        19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      sieveM x ≤
          ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
            18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := hM
      _ ≤ ((x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
            18 * ((x : ℝ) *
              (x : ℝ) ^ ((1 : ℝ) / 100))) *
              (x : ℝ) ^ ((1 : ℝ) / 100) := by
        exact mul_le_mul hinside hlog
          (by linarith) (by positivity)
      _ = 19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by ring
  calc
    (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x ≤
        (x : ℝ) ^ (-(0.1 : ℝ)) *
          (19 * (x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hM'
        (Real.rpow_nonneg hxpos.le _)
    _ = 19 * ((x : ℝ) ^ (-(0.1 : ℝ)) *
          (x : ℝ) ^ (1 : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      rw [Real.rpow_one]
      ring
    _ = 19 * (x : ℝ) ^ ((92 : ℝ) / 100) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
        ← Real.rpow_add hxpos]
      congr 2
      norm_num
    _ ≤ 19 * ((x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [show (92 : ℝ) / 100 =
          1 - (8 : ℝ) / 100 by norm_num] using hpower
    _ = 19 * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by ring

/-- The Selberg divisor sum over positive divisors of `a` which are coprime
to `x`.  The finite ambient range contains the support of every sieve
weight used below. -/
noncomputable def sieveDivisorSum
    (x : ℕ) (ε : ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ (Finset.range (x + 1)).filter fun d =>
      1 ≤ d ∧ d.Coprime x ∧ d ∣ a,
    sieveWeight x ε d

/-- Positive divisor indices, coprime to `x`, in the common finite ambient
range used to expand the square sieve. -/
def sieveDivisorUniverse (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d => 1 ≤ d ∧ d.Coprime x

/-- Indicator form of the divisor sum, convenient for expanding its
square. -/
theorem sieveDivisorSum_eq_sum_universe
    (x : ℕ) (ε : ℝ) (a : ℕ) :
    sieveDivisorSum x ε a =
      ∑ d ∈ sieveDivisorUniverse x,
        if d ∣ a then sieveWeight x ε d else 0 := by
  unfold sieveDivisorSum sieveDivisorUniverse
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdpos : 1 ≤ d
  · by_cases hdcop : d.Coprime x
    · by_cases hda : d ∣ a
      · simp [hdpos, hda]
      · simp [hdpos, hda]
    · simp [hdpos, hdcop]
  · simp [hdpos]

/-- A pair of nonzero sieve weights in the divisor universe has its lcm in
the collected modulus range. -/
theorem lcm_mem_sieveModuli_of_sieveWeight_mul_ne_zero
    {x d₁ d₂ : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hd₁ : d₁ ∈ sieveDivisorUniverse x)
    (hd₂ : d₂ ∈ sieveDivisorUniverse x)
    (hweight :
      sieveWeight x ε d₁ * sieveWeight x ε d₂ ≠ 0) :
    d₁.lcm d₂ ∈ sieveModuli x ε := by
  have hd₁data := (Finset.mem_filter.mp hd₁).2
  have hd₂data := (Finset.mem_filter.mp hd₂).2
  have hd₁pos : 0 < d₁ := by omega
  have hd₂pos : 0 < d₂ := by omega
  have hweight₁ : sieveWeight x ε d₁ ≠ 0 := by
    intro h
    exact hweight (by rw [h, zero_mul])
  have hweight₂ : sieveWeight x ε d₂ ≠ 0 := by
    intro h
    exact hweight (by rw [h, mul_zero])
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hexp0 : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hRone :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) :=
    Real.one_le_rpow hxone hexp0
  have hd₁cut :
      (d₁ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hweight₁ with h | h
    · simpa only [h, Nat.cast_one] using hRone
    · exact h
  have hd₂cut :
      (d₂ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hweight₂ with h | h
    · simpa only [h, Nat.cast_one] using hRone
    · exact h
  have hlcmpos : 0 < d₁.lcm d₂ := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz := Nat.lcm_eq_zero_iff.mp h
    omega
  have hlcmcop : (d₁.lcm d₂).Coprime x :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d₁ d₂)
      (hd₁data.2.mul_left hd₂data.2)
  have hlcmle : d₁.lcm d₂ ≤ d₁ * d₂ :=
    Nat.lcm_le_mul hd₁pos hd₂pos
  have hprod :
      ((d₁ * d₂ : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    norm_num only [Nat.cast_mul]
    exact mul_le_mul hd₁cut hd₂cut (by positivity) (by positivity)
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) =
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hlcmcut :
      (d₁.lcm d₂ : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    calc
      (d₁.lcm d₂ : ℝ) ≤ (d₁ * d₂ : ℕ) := by
        exact_mod_cast hlcmle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hprod
      _ = (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow
  have hexp_le : (1 : ℝ) / 2 - ε ≤ 1 := by linarith
  have hlcmx : d₁.lcm d₂ ≤ x := by
    have hpowx :
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hxone hexp_le
    exact_mod_cast hlcmcut.trans hpowx
  simp only [sieveModuli, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by exact ⟨by omega, hlcmcop, hlcmcut⟩⟩

/-- Collecting the expanded square of the divisor sum by
`lcm(d₁,d₂)` gives exactly `sieveLcmCoeff`. -/
theorem sieveDivisorSum_sq_eq_lcm_sum
    {x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    (sieveDivisorSum x ε a) ^ 2 =
      ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          (if d ∣ a then 1 else 0) := by
  let U : Finset ℕ := sieveDivisorUniverse x
  let P : Finset (ℕ × ℕ) := U ×ˢ U
  let f : ℕ × ℕ → ℝ := fun q =>
    (if q.1 ∣ a then sieveWeight x ε q.1 else 0) *
      (if q.2 ∣ a then sieveWeight x ε q.2 else 0)
  have hsquare :
      (sieveDivisorSum x ε a) ^ 2 =
        ∑ q ∈ P, f q := by
    rw [sieveDivisorSum_eq_sum_universe, pow_two,
      Finset.sum_mul_sum]
    simp only [P, U, f, Finset.sum_product]
  have hsupport :
      ∑ q ∈ P, f q =
        ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hlcm :
        q.1.lcm q.2 ∈ sieveModuli x ε
    · simp [hlcm]
    · rw [if_neg hlcm]
      by_contra hf
      have hqdata := Finset.mem_product.mp hq
      have hweight :
          sieveWeight x ε q.1 *
            sieveWeight x ε q.2 ≠ 0 := by
        apply mul_ne_zero
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
      exact hlcm
        (lcm_mem_sieveModuli_of_sieveWeight_mul_ne_zero
          hx1 hε0 hεhalf
          (by simpa only [U] using hqdata.1)
          (by simpa only [U] using hqdata.2) hweight)
  have hfiber :
      ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q =
        ∑ d ∈ sieveModuli x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := by
    symm
    exact Finset.sum_fiberwise_eq_sum_filter P
      (sieveModuli x ε) (fun q => q.1.lcm q.2) f
  calc
    (sieveDivisorSum x ε a) ^ 2 =
        ∑ q ∈ P, f q := hsquare
    _ = ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q := hsupport
    _ = ∑ d ∈ sieveModuli x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := hfiber
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          (if d ∣ a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddata := (Finset.mem_filter.mp hd).2
      have hdpos : 0 < d := by omega
      have hdle : d ≤ x := by
        have hdrange := (Finset.mem_filter.mp hd).1
        have hdlt := Finset.mem_range.mp hdrange
        omega
      have hfin :
          P.filter (fun q => q.1.lcm q.2 = d) =
            (d.divisors ×ˢ d.divisors).filter
              (fun q => q.1.lcm q.2 = d) := by
        ext q
        simp only [P, U, sieveDivisorUniverse,
          Finset.mem_filter, Finset.mem_product,
          Finset.mem_range]
        constructor
        · intro h
          rcases h with
            ⟨⟨⟨hq₁range, hq₁pos, hq₁cop⟩,
              ⟨hq₂range, hq₂pos, hq₂cop⟩⟩, hlcm⟩
          have hq₁d : q.1 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_left q.1 q.2
          have hq₂d : q.2 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_right q.1 q.2
          exact ⟨⟨Nat.mem_divisors.mpr ⟨hq₁d, hdpos.ne'⟩,
            Nat.mem_divisors.mpr ⟨hq₂d, hdpos.ne'⟩⟩, hlcm⟩
        · intro h
          rcases h with ⟨⟨hq₁mem, hq₂mem⟩, hlcm⟩
          have hq₁d := Nat.dvd_of_mem_divisors hq₁mem
          have hq₂d := Nat.dvd_of_mem_divisors hq₂mem
          have hq₁pos : 1 ≤ q.1 :=
            Nat.pos_of_dvd_of_pos hq₁d hdpos
          have hq₂pos : 1 ≤ q.2 :=
            Nat.pos_of_dvd_of_pos hq₂d hdpos
          have hq₁cop :=
            Nat.Coprime.of_dvd_left hq₁d hddata.2.1
          have hq₂cop :=
            Nat.Coprime.of_dvd_left hq₂d hddata.2.1
          have hq₁le : q.1 ≤ d := Nat.le_of_dvd hdpos hq₁d
          have hq₂le : q.2 ≤ d := Nat.le_of_dvd hdpos hq₂d
          exact
            ⟨⟨⟨by omega, hq₁pos, hq₁cop⟩,
              ⟨by omega, hq₂pos, hq₂cop⟩⟩, hlcm⟩
      rw [hfin, sieveLcmCoeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hlcm := (Finset.mem_filter.mp hq).2
      have hqdiv := Finset.mem_product.mp
        (Finset.mem_filter.mp hq).1
      have hq₁d := Nat.dvd_of_mem_divisors hqdiv.1
      have hq₂d := Nat.dvd_of_mem_divisors hqdiv.2
      by_cases hda : d ∣ a
      · have hq₁a : q.1 ∣ a := dvd_trans hq₁d hda
        have hq₂a : q.2 ∣ a := dvd_trans hq₂d hda
        simp [f, hda, hq₁a, hq₂a]
      · have hnotboth : ¬(q.1 ∣ a ∧ q.2 ∣ a) := by
          intro h
          apply hda
          rw [← hlcm]
          exact Nat.lcm_dvd h.1 h.2
        rcases not_and_or.mp hnotboth with hq₁a | hq₂a
        · simp [f, hda, hq₁a]
        · simp [f, hda, hq₂a]

/-- On an `x^(1/4)`-rough integer, the only nonzero divisor weight is
`λ₁ = 1`. -/
theorem sieveDivisorSum_eq_one_of_rough
    {x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (ha : chenRough x a) :
    sieveDivisorSum x ε a = 1 := by
  unfold sieveDivisorSum
  let S : Finset ℕ :=
    (Finset.range (x + 1)).filter fun d =>
      1 ≤ d ∧ d.Coprime x ∧ d ∣ a
  have h1S : 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simp⟩
  calc
    ∑ d ∈ (Finset.range (x + 1)).filter (fun d =>
        1 ≤ d ∧ d.Coprime x ∧ d ∣ a),
        sieveWeight x ε d =
      ∑ d ∈ S, sieveWeight x ε d := by rfl
    _ = sieveWeight x ε 1 := by
      apply Finset.sum_eq_single 1
      · intro d hdS hd1
        by_contra hweight
        have hddata := (Finset.mem_filter.mp hdS).2
        have hdpos : 0 < d := by omega
        obtain ⟨p, hp, hpd⟩ :=
          Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hp_le_d : p ≤ d := Nat.le_of_dvd hdpos hpd
        have hdcut := (sieveWeight_support hweight).resolve_left hd1
        have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
        have hexp :
            (1 : ℝ) / 4 - ε / 2 ≤ (1 : ℝ) / 4 := by
          linarith
        have hdquarter :
            (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          hdcut.trans
            (Real.rpow_le_rpow_of_exponent_le hxone hexp)
        have hpquarter :
            (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          (show (p : ℝ) ≤ d by exact_mod_cast hp_le_d).trans
            hdquarter
        exact ha p hp hpquarter
          (dvd_trans hpd hddata.2.2)
      · intro hnot
        exact (hnot h1S).elim
    _ = 1 := sieveWeight_one x ε

/-- Every smoothed kernel is nonnegative on an admissible prime pair. -/
theorem smoothedMKernel_nonneg
    {x n : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) :
    0 ≤ smoothedMKernel x q n := by
  unfold smoothedMKernel
  have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    one_lt_pairQuotient hq
  have hlog : 0 < Real.log
      ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
    Real.log_pos hY
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr hlog.le)
      ArithmeticFunction.vonMangoldt_nonneg)
    (chenPhi_nonneg x (by exact_mod_cast hx) hy)

/-- Formula (5) before collecting the two divisor variables by their lcm. -/
noncomputable def squareSieveExpansion
    (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ smoothedMIndices x q,
      smoothedMKernel x q n *
        (sieveDivisorSum x ε (x - q.1 * q.2 * n)) ^ 2

/-- The smoothed rough sum is the same finite sum written with
`smoothedMKernel`. -/
theorem smoothedRoughM_eq_kernel_sum (x : ℕ) :
    smoothedRoughM x =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ sieveMIndices x q,
          smoothedMKernel x q n := by
  unfold smoothedRoughM smoothedMKernel
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The square Selberg divisor sum majorizes the roughness indicator
pointwise. -/
theorem smoothedRoughM_le_squareSieveExpansion
    {x : ℕ} {ε : ℝ} (hx : 1 < x) (hε0 : 0 ≤ ε) :
    smoothedRoughM x ≤ squareSieveExpansion x ε := by
  rw [smoothedRoughM_eq_kernel_sum]
  unfold squareSieveExpansion
  apply Finset.sum_le_sum
  intro q hq
  have hsubset :
      sieveMIndices x q ⊆ smoothedMIndices x q := by
    intro n hn
    have hn' := hn
    simp only [sieveMIndices, Finset.mem_filter,
      Finset.mem_range] at hn'
    simp only [smoothedMIndices, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hn'.1, hn'.2.1⟩
  calc
    ∑ n ∈ sieveMIndices x q, smoothedMKernel x q n =
        ∑ n ∈ sieveMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := hn
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      rw [sieveDivisorSum_eq_one_of_rough
        (show 1 ≤ x by omega) hε0 hn'.2.2]
      ring
    _ ≤ ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnrough
      exact mul_nonneg (smoothedMKernel_nonneg hx hq) (sq_nonneg _)

/-- The uncollected square-sieve expansion is exactly the existing
`smoothedSieveExpansion`, whose divisor pairs are collected by their lcm. -/
theorem squareSieveExpansion_eq_smoothedSieveExpansion
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    squareSieveExpansion x ε =
      smoothedSieveExpansion x ε := by
  unfold squareSieveExpansion smoothedSieveExpansion
  calc
    ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            ∑ d ∈ sieveModuli x ε,
              sieveLcmCoeff x ε d *
                (if x ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro n hn
      have hm : q.1 * q.2 * n ≤ x :=
        smoothedMArgument_le hq hn
      have hsquare :=
        sieveDivisorSum_sq_eq_lcm_sum
          (x := x) (a := x - q.1 * q.2 * n)
          (ε := ε) hx1 hε0 hεhalf
      rw [hsquare]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hiff :
          x ≡ q.1 * q.2 * n [MOD d] ↔
            d ∣ x - q.1 * q.2 * n :=
        Nat.ModEq.comm.trans (Nat.modEq_iff_dvd' hm)
      by_cases hmod : x ≡ q.1 * q.2 * n [MOD d]
      · have hdvd := hiff.mp hmod
        simp [hmod, hdvd]
      · have hndvd : ¬d ∣ x - q.1 * q.2 * n := by
          intro hdvd
          exact hmod (hiff.mpr hdvd)
        simp [hmod, hndvd]
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                (if x ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      calc
        (∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                ∑ d ∈ sieveModuli x ε,
                  sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) =
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              ∑ d ∈ sieveModuli x ε,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
        _ =
          ∑ q ∈ chenPairs x,
            ∑ d ∈ sieveModuli x ε,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]
        _ = ∑ d ∈ sieveModuli x ε,
            ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            rw [Finset.sum_comm]
        _ = ∑ d ∈ sieveModuli x ε,
            sieveLcmCoeff x ε d *
              ∑ q ∈ chenPairs x,
                ∑ n ∈ smoothedMIndices x q,
                  smoothedMKernel x q n *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          ∑ z ∈ smoothedMTriples x,
            smoothedMKernel x z.1 z.2 *
              (if x ≡ smoothedMArgument z [MOD d]
                then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      exact (sum_smoothedMTriples_eq_nested x
        (fun q n =>
          smoothedMKernel x q n *
            (if x ≡ q.1 * q.2 * n [MOD d]
              then 1 else 0))).symm

/-- Finite square-sieve form of the second inequality in formula (5). -/
theorem smoothedRoughM_le_smoothedSieveExpansion
    {x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    smoothedRoughM x ≤ smoothedSieveExpansion x ε := by
  calc
    smoothedRoughM x ≤ squareSieveExpansion x ε :=
      smoothedRoughM_le_squareSieveExpansion hx hε0
    _ = smoothedSieveExpansion x ε :=
      squareSieveExpansion_eq_smoothedSieveExpansion
        (show 1 ≤ x by omega) hε0 hεhalf

/-- Formula (5) with its analytic smoothing error left explicit. -/
theorem sieveM_le_smoothedSieveExpansion_add_smoothingError
    {x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    sieveM x ≤
      smoothedSieveExpansion x ε + sieveMSmoothingError x := by
  rw [sieveM_eq_smoothedRoughM_add_smoothingError]
  simpa [add_comm] using
    add_le_add_right
      (smoothedRoughM_le_smoothedSieveExpansion
        hx hε0 hεhalf) (sieveMSmoothingError x)

end Chen
