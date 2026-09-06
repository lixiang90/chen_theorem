import ChenTheorem.Lemma9.LinearSieve.SieveParameter

open Finset MeasureTheory

namespace Chen.LinearSieve

theorem hasDerivAt_sieveParameter_weight (D t : ℝ) (ht : 1 < t)
    (H : ℝ → ℝ) (hH : DifferentiableAt ℝ H (sieveParameter D t)) :
    HasDerivAt (fun t => H (sieveParameter D t))
      (deriv H (sieveParameter D t) * (-Real.log D * logSieveKernel t)) t :=
  hH.hasDerivAt.comp t (hasDerivAt_sieveParameter D t ht)

theorem integrableOn_sieveParameter_weight_deriv (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (H : ℝ → ℝ)
    (hHd : ∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), DifferentiableAt ℝ H s)
    (hHc : ContinuousOn (deriv H) (Set.Icc (sieveParameter D z) (sieveParameter D w))) :
    IntegrableOn (deriv (fun t => H (sieveParameter D t))) (Set.Icc w z) := by
  have hcomp := hHc.comp (continuousOn_sieveParameter D w z hw)
    (fun t ht => sieveParameter_mem_Icc hD hw ht)
  have hc : ContinuousOn (fun t => deriv H (sieveParameter D t) *
      (-Real.log D * logSieveKernel t)) (Set.Icc w z) :=
    hcomp.mul (continuousOn_const.mul (continuousOn_logSieveKernel w z hw))
  have hi : IntegrableOn (fun t => deriv H (sieveParameter D t) *
      (-Real.log D * logSieveKernel t)) (Set.Icc w z) := hc.integrableOn_Icc
  apply hi.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hasDerivAt_sieveParameter_weight D t (by linarith [ht.1]) H
    (hHd _ (sieveParameter_mem_Icc hD hw ht))).deriv.symm

/-- The conventional monotonicity of `s H(s)` gives exactly the
logarithmic growth condition used in weighted partial summation. -/
theorem sieveParameter_weight_log_growth (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (hwz : w ≤ z) (H : ℝ → ℝ)
    (hH : AntitoneOn (fun s => s * H s)
      (Set.Icc (sieveParameter D z) (sieveParameter D w))) :
    ∀ t ∈ Set.Icc w z, H (sieveParameter D t) * Real.log z ≤
      H (sieveParameter D z) * Real.log t := by
  intro t ht
  have hst := sieveParameter_mem_Icc hD hw ht
  have hsz := sieveParameter_mem_Icc hD hw (show z ∈ Set.Icc w z from ⟨hwz, le_rfl⟩)
  have hs := hH hsz hst hst.1
  have hL : 0 < Real.log D := Real.log_pos hD
  have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs' : Real.log D * (H (sieveParameter D t) / Real.log t) ≤
      Real.log D * (H (sieveParameter D z) / Real.log z) := by
    simpa only [sieveParameter, div_mul_eq_mul_div, mul_div_assoc] using hs
  exact (div_le_div_iff₀ hlt hlz).mp ((mul_le_mul_iff_right₀ hL).mp hs')

/-- Partial summation in the sieve parameter: for `s = log D/log z`
and `σ = log D/log w`, the main term is `(1/s) ∫_s^σ H`.
All regularity and shape assumptions on `H` are explicit. -/
theorem weighted_buchstab_parameter_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ H : ℝ → ℝ,
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), DifferentiableAt ℝ H s) →
        ContinuousOn (deriv H) (Set.Icc (sieveParameter D z) (sieveParameter D w)) →
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), 0 ≤ H s) →
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), deriv H s ≤ 0) →
        AntitoneOn (fun s => s * H s) (Set.Icc (sieveParameter D z) (sieveParameter D w)) →
        (∑ p ∈ Ioc ⌊w⌋₊ z, H (sieveParameter D p) * buchstabCoefficient P z p) ≤
          (1 / sieveParameter D z) *
            (∫ s in Set.Ioc (sieveParameter D z) (sieveParameter D w), H s) +
              2 * K * H (sieveParameter D z) / Real.log w := by
  obtain ⟨K, hK, hbound⟩ := weighted_buchstab_partial_summation
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz P hP hodd H hHd hHc hH0 hHderiv hHshape
  have hfd : ∀ t ∈ Set.Icc w (z : ℝ),
      DifferentiableAt ℝ (fun t => H (sieveParameter D t)) t := by
    intro t ht
    exact (hasDerivAt_sieveParameter_weight D t (by linarith [ht.1]) H
      (hHd _ (sieveParameter_mem_Icc hD hw ht))).differentiableAt
  have hfderiv : ∀ t ∈ Set.Icc w (z : ℝ),
      0 ≤ deriv (fun t => H (sieveParameter D t)) t := by
    intro t ht
    rw [(hasDerivAt_sieveParameter_weight D t (by linarith [ht.1]) H
      (hHd _ (sieveParameter_mem_Icc hD hw ht))).deriv]
    apply mul_nonneg_of_nonpos_of_nonpos (hHderiv _ (sieveParameter_mem_Icc hD hw ht))
    have hkernel : 0 ≤ logSieveKernel t := by
      have ht0 : 0 < t := by linarith [ht.1]
      unfold logSieveKernel
      positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.log_pos hD).le) hkernel
  have hb := hbound w z hw hwz P hP hodd (fun t => H (sieveParameter D t)) hfd
    (integrableOn_sieveParameter_weight_deriv D w z hD hw H hHd hHc)
    (fun t ht => hH0 _ (sieveParameter_mem_Icc hD hw ht)) hfderiv
    (sieveParameter_weight_log_growth D w z hD hw hwz H hHshape)
  rwa [integral_sieveParameter_substitution D w z hD hw hwz H
    (fun s hs => (hHd s hs).continuousAt.continuousWithinAt)] at hb

end Chen.LinearSieve
