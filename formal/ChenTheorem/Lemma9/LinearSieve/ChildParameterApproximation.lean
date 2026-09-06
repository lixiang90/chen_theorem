import ChenTheorem.Lemma9.LinearSieve.PowerParameterLimits
import ChenTheorem.Lemma9.LinearSieve.MidPrimeSumLimit

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

theorem eventually_log_childLevel_error_le (a : ℝ) (ha : 1 / 3 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x,
      |Real.log (powerSieveCutoff a x / p : ℕ) / Real.log x -
        (a - normalizedLog x p)| ≤ Real.log 4 / Real.log x := by
  filter_upwards [eventually_powerSieveCutoff_div_midPrime a ha,
    ((tendsto_rpow_atTop (show 0 < a by linarith)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (2 : ℕ)] with x hmid hpow hx
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hQ : 2 * p ≤ powerSieveCutoff a x :=
    (Nat.le_div_iff_mul_le hprime.pos).mp (show 2 ≤ powerSieveCutoff a x / p by have := hmid p hp; omega)
  have hb := log_roundedChildLevel_bounds a x p (by omega) hprime.pos hpow hQ
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hh : |Real.log (powerSieveCutoff a x / p : ℕ) - (a * Real.log x - Real.log p)| ≤ Real.log 4 := by
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  unfold normalizedLog
  calc
    _ = |(Real.log (powerSieveCutoff a x / p : ℕ) - (a * Real.log x - Real.log p)) / Real.log x| := by
      congr 1
      field_simp
    _ ≤ _ := by
      rw [abs_div, abs_of_pos hL]
      exact div_le_div_of_nonneg_right hh hL.le

theorem eventually_childLevel_ge (a M : ℝ) (ha : 1 / 3 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x, M ≤ (powerSieveCutoff a x / p : ℕ) := by
  have hgrow : Tendsto (fun x : ℕ => (x : ℝ) ^ (a - 1 / 3) / 4) atTop atTop :=
    (((tendsto_rpow_atTop (by linarith : 0 < a - 1 / 3)).comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num))
  filter_upwards [eventually_powerSieveCutoff_div_midPrime a ha,
    ((tendsto_rpow_atTop (show 0 < a by linarith)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ)), hgrow.eventually (eventually_ge_atTop M),
    eventually_ge_atTop (2 : ℕ)] with x hmid hpow hM hx
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hQ : 2 * p ≤ powerSieveCutoff a x :=
    (Nat.le_div_iff_mul_le hp'.1.pos).mp (show 2 ≤ powerSieveCutoff a x / p by have := hmid p hp; omega)
  have hb := (roundedChildLevel_bounds a x p hp'.1.pos hpow hQ).1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
  calc
    M ≤ (x : ℝ) ^ (a - 1 / 3) / 4 := hM
    _ = (x : ℝ) ^ a / (4 * (x : ℝ) ^ (1 / 3 : ℝ)) := by
      rw [Real.rpow_sub hx0]
      ring
    _ ≤ (x : ℝ) ^ a / (4 * p) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (by positivity)
        (mul_le_mul_of_nonneg_left hp'.2.2 (by norm_num))
    _ ≤ _ := hb

theorem eventually_childSieveParameter_error_lt (a ε : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ midPrimes x,
      |sieveParameter (powerSieveCutoff a x / p : ℕ) ((powerSieveCutoff (1 / 10) x : ℝ) + 1) -
        (10 * a - 10 * normalizedLog x p)| < ε := by
  let R : ℕ → ℝ := fun x => Real.log x / Real.log ((powerSieveCutoff (1 / 10) x : ℝ) + 1)
  have hlim : Tendsto (fun x : ℕ => 11 * (Real.log 4 / Real.log x) + |R x - 10|) atTop (𝓝 0) := by
    have he : Tendsto (fun x : ℕ => Real.log 4 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hr := (log_div_smallCutoff_succ_tendsto.sub_const 10).abs
    simpa only [mul_zero, sub_self, abs_zero, zero_add] using (he.const_mul 11).add hr
  filter_upwards [eventually_log_childLevel_error_le a (by linarith),
    hlim.eventually (gt_mem_nhds hε),
    log_div_smallCutoff_succ_tendsto.eventually (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) < 11)),
    eventually_ge_atTop (2 : ℕ)] with x hlog herr hR hx
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hα := normalizedLog_power_interval x p hxR ⟨hp'.2.1.le, hp'.2.2⟩
  have hc : |a - normalizedLog x p| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hα.1, hα.2]
  have hL : Real.log (x : ℝ) ≠ 0 := (Real.log_pos hxR).ne'
  have hR0 : 0 < R x := hR.1
  have hR11 : R x ≤ 11 := hR.2.le
  have hdecomp : sieveParameter (powerSieveCutoff a x / p : ℕ)
      ((powerSieveCutoff (1 / 10) x : ℝ) + 1) - (10 * a - 10 * normalizedLog x p) =
      R x * (Real.log (powerSieveCutoff a x / p : ℕ) / Real.log x - (a - normalizedLog x p)) +
        (R x - 10) * (a - normalizedLog x p) := by
    unfold sieveParameter R
    field_simp
    ring
  rw [hdecomp]
  calc
    _ ≤ |R x * (Real.log (powerSieveCutoff a x / p : ℕ) / Real.log x - (a - normalizedLog x p))| +
        |(R x - 10) * (a - normalizedLog x p)| := abs_add_le _ _
    _ ≤ 11 * (Real.log 4 / Real.log x) + |R x - 10| := by
      rw [abs_mul, abs_of_pos hR0, abs_mul]
      apply add_le_add
      · exact mul_le_mul hR11 (hlog p hp) (abs_nonneg _) (by norm_num)
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (abs_nonneg (R x - 10))
    _ < ε := herr

end Chen.LinearSieve
