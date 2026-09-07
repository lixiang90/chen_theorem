import Submission.ChenTheorem.Lemma9.LinearSieve.ChildParameterApproximation
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserAsymptoticError

set_option autoImplicit true
open Set Filter
open scoped Topology

namespace Chen.LinearSieve

theorem eventually_childSieveParameter_compact (a : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x,
      sieveParameter (powerSieveCutoff a x / p : ℕ)
        ((powerSieveCutoff (1 / 10) x : ℝ) + 1) ∈ Icc (5 / 4) 5 := by
  filter_upwards [eventually_childSieveParameter_error_lt a (1 / 4) ha ha' (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with x herr hx
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hα := normalizedLog_power_interval x p
    (by exact_mod_cast (show 1 < x by omega)) ⟨hp'.2.1.le, hp'.2.2⟩
  have he := abs_lt.mp (herr p hp)
  constructor <;> linarith [hα.1, hα.2, he.1, he.2]

theorem eventually_upperSieveChildWeight_error_lt (a ε : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x,
      |upperLinearSieveFunction (sieveParameter (powerSieveCutoff a x / p : ℕ)
        ((powerSieveCutoff (1 / 10) x : ℝ) + 1)) - upperSievePrimeWeight a x p| < ε := by
  have hc : ContinuousOn upperLinearSieveFunction (Icc (5 / 4 : ℝ) 5) :=
    continuousOn_upperLinearSieveFunction.mono (fun s hs => by
      change 1 < s
      linarith [hs.1])
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  filter_upwards [eventually_childSieveParameter_compact a ha ha',
    eventually_childSieveParameter_error_lt a δ ha ha' hδ,
    eventually_ge_atTop (2 : ℕ)] with x hcomp herr hx
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hα := normalizedLog_power_interval x p
    (by exact_mod_cast (show 1 < x by omega)) ⟨hp'.2.1.le, hp'.2.2⟩
  have htarget : 10 * a - 10 * normalizedLog x p ∈ Icc (5 / 4 : ℝ) 5 := by
    constructor <;> linarith [hα.1, hα.2]
  exact hclose _ (hcomp p hp) _ htarget (by simpa only [Real.dist_eq] using herr p hp)

/-- The actual child Rosser polynomial is bounded uniformly over all middle primes
by the continuous weight used in Chen's prime sum. -/
theorem eventually_rosser_upper_child_power (a ε : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x, ∀ P : Finset ℕ,
      (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      rosserEval P primeDensity (powerSieveCutoff (1 / 10) x + 1) true
        (powerSieveCutoff a x / p : ℕ) ≤
      sieveProduct P primeDensity (powerSieveCutoff (1 / 10) x + 1) *
        (upperSievePrimeWeight a x p + ε) := by
  obtain ⟨M, hM⟩ := (eventually_atTop.1
    (eventually_rosser_upper_polynomial_compact (5 / 4) 5 (ε / 2)
      (by norm_num) (by norm_num) (half_pos hε)))
  filter_upwards [eventually_childLevel_ge a M (by linarith),
    eventually_childSieveParameter_compact a ha ha',
    eventually_upperSieveChildWeight_error_lt a (ε / 2) ha ha' (half_pos hε),
    (powerSieveCutoff_tendsto (1 / 10) (by norm_num)).eventually (eventually_ge_atTop 2)]
    with x hlevel hcomp herr hz
  intro p hp P hP hodd
  have hb := hM _ (hlevel p hp) _ hz (hcomp p hp).1 (hcomp p hp).2 P hP hodd
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (primeDensity_sieveProduct_pos P hP hodd _).le
  have he := (abs_lt.mp (herr p hp)).2
  linarith

/-- The parent lower Rosser polynomial at the same rounded power level. -/
theorem eventually_rosser_lower_parent_power (a ε : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      sieveProduct P primeDensity (powerSieveCutoff (1 / 10) x + 1) *
        (lowerLinearSieveFunction (10 * a) - ε) ≤
      rosserEval P primeDensity (powerSieveCutoff (1 / 10) x + 1) false
        (powerSieveCutoff a x) := by
  have hs := sieveParameter_powerSieveCutoff_tendsto a (by linarith)
  have hf := (continuousOn_lowerLinearSieveFunction.continuousAt
    (Ici_mem_nhds (show (2 : ℝ) < 10 * a by linarith))).tendsto.comp hs
  have herr := (tendsto_order.1 hf).1
    (lowerLinearSieveFunction (10 * a) - ε / 2) (by linarith)
  have hlevel : Tendsto (fun x : ℕ => (powerSieveCutoff a x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (powerSieveCutoff_tendsto a (by linarith))
  filter_upwards [hlevel.eventually
      (eventually_rosser_lower_polynomial_compact 4 6 (ε / 2)
        (by norm_num) (by norm_num) (half_pos hε)),
    hs.eventually (Ioo_mem_nhds (show (4 : ℝ) < 10 * a by linarith)
      (show 10 * a < (6 : ℝ) by linarith)), herr,
    (powerSieveCutoff_tendsto (1 / 10) (by norm_num)).eventually (eventually_ge_atTop 2)]
    with x hb hcomp he hz
  intro P hP hodd
  apply le_trans _ (hb _ hz hcomp.1.le hcomp.2.le P hP hodd)
  apply mul_le_mul_of_nonneg_left _ (primeDensity_sieveProduct_pos P hP hodd _).le
  change lowerLinearSieveFunction (10 * a) - ε / 2 <
    lowerLinearSieveFunction (sieveParameter (powerSieveCutoff a x)
      ((powerSieveCutoff (1 / 10) x : ℝ) + 1)) at he
  linarith

end Chen.LinearSieve
