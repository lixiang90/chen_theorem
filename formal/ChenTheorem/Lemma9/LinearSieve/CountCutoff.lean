import ChenTheorem.Lemma9.LinearSieve.ChenPrimeCounts

open Filter
open scoped Classical

namespace Chen.LinearSieve

/-- Cutoff used when removing logarithmic prime weights. Its contribution
to the count loss is two logarithmic powers smaller than the target scale. -/
noncomputable def countCutoff (x : ℕ) : ℝ := (x : ℝ) / (Real.log x) ^ 4

/-- The lower logarithmic cutoff approaches the endpoint logarithm.
This makes the unequal denominators in the ordinary-count conversion
compatible with an arbitrarily small loss in the main constant. -/
theorem eventually_log_countCutoff (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) :
    ∀ᶠ x : ℕ in atTop,
      1 < countCutoff x ∧
      (1 - ε) * Real.log x ≤ Real.log (countCutoff x) := by
  have hsmall := Real.isLittleO_log_id_atTop.def (show 0 < ε / 4 by positivity)
  have hlogT := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogT.eventually hsmall,
    hlogT.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (2 : ℕ)] with x hx hlog hx2
  change 1 ≤ Real.log (x : ℝ) at hlog
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hloglog : 0 ≤ Real.log (Real.log (x : ℝ)) := Real.log_nonneg hlog
  have hsmall' : Real.log (Real.log (x : ℝ)) ≤ (ε / 4) * Real.log (x : ℝ) := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg hloglog, abs_of_nonneg hlogpos.le] using hx
  have hcutpos : 0 < countCutoff x := by unfold countCutoff; positivity
  have heq : Real.log (countCutoff x) = Real.log x - 4 * Real.log (Real.log x) := by
    rw [countCutoff, Real.log_div (ne_of_gt hxpos) (pow_ne_zero _ (ne_of_gt hlogpos)), Real.log_pow]
    norm_num
  have hlower : (1 - ε) * Real.log x ≤ Real.log (countCutoff x) := by rw [heq]; nlinarith
  have hcutlog : 0 < Real.log (countCutoff x) :=
    (mul_pos (by linarith) hlogpos).trans_le hlower
  have hcutone := Real.one_lt_exp_iff.mpr hcutlog
  rw [Real.exp_log hcutpos] at hcutone
  exact ⟨hcutone, hlower⟩

/-- The ceiling in the finite count conversion costs at most one extra
integer; it does not alter the logarithmic saving of the cutoff. -/
theorem ceil_countCutoff_le {x : ℕ} (hx : 1 < x) :
    (⌈countCutoff x⌉₊ : ℝ) ≤ (x : ℝ) / (Real.log x) ^ 4 + 1 := by
  have hnonneg : 0 ≤ countCutoff x := by unfold countCutoff; positivity
  exact le_of_lt (Nat.ceil_lt_add_one hnonneg)

/-- Removing the small-prime cutoff changes a logarithmic denominator
by a factor tending to one. -/
theorem log_countCutoff_div_log_tendsto :
    Tendsto (fun x : ℕ => Real.log (countCutoff x) / Real.log x) atTop (nhds 1) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hsmall.const_mul 4)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  dsimp only [Function.comp_apply, id_eq]
  rw [countCutoff, Real.log_div (ne_of_gt hxpos) (pow_ne_zero _ (ne_of_gt hlpos)),
    Real.log_pow]
  push_cast
  field_simp

theorem log_div_log_countCutoff_tendsto :
    Tendsto (fun x : ℕ => Real.log x / Real.log (countCutoff x)) atTop (nhds 1) := by
  simpa only [inv_one, inv_div] using log_countCutoff_div_log_tendsto.inv₀ one_ne_zero

end Chen.LinearSieve
