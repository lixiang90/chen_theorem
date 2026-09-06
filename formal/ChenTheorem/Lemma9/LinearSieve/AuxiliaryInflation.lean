import ChenTheorem.Lemma9.LinearSieve.AuxiliaryLevelError

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The additional factor used to make the auxiliary error uniform in
the sieve parameter. The power `d` is a real parameter. -/
noncomputable def auxiliaryInflation (d D s : ℝ) : ℝ :=
  (1 + s ^ d / Real.log D) ^ s

/-- A child level retains the parent base, but has exponent one smaller. -/
noncomputable def auxiliaryChildInflation (d D s : ℝ) : ℝ :=
  (1 + s ^ d / Real.log D) ^ (s - 1)

theorem auxiliaryInflation_pos (d D s : ℝ) (hD : 1 < D) (hs : 0 ≤ s) :
    0 < auxiliaryInflation d D s := by
  apply Real.rpow_pos_of_pos
  have hn := div_nonneg (Real.rpow_nonneg hs d) (Real.log_pos hD).le
  linarith

theorem one_le_auxiliaryInflation (d D s : ℝ) (hD : 1 < D) (hs : 0 ≤ s) :
    1 ≤ auxiliaryInflation d D s := by
  exact Real.one_le_rpow (by
    have := div_nonneg (Real.rpow_nonneg hs d) (Real.log_pos hD).le
    linarith) hs

theorem monotoneOn_auxiliaryInflation (d D : ℝ) (hd : 0 ≤ d) (hD : 1 < D) :
    MonotoneOn (auxiliaryInflation d D) (Ici 0) := by
  intro s hs t ht hst
  have hbase : 1 + s ^ d / Real.log D ≤ 1 + t ^ d / Real.log D :=
    _root_.add_le_add le_rfl (div_le_div_of_nonneg_right (Real.rpow_le_rpow hs hst hd)
      (Real.log_pos hD).le)
  have hb : 1 ≤ 1 + t ^ d / Real.log D := by
    have := div_nonneg (Real.rpow_nonneg ht d) (Real.log_pos hD).le
    linarith
  exact (Real.rpow_le_rpow (by
    have := div_nonneg (Real.rpow_nonneg hs d) (Real.log_pos hD).le
    linarith) hbase hs).trans (Real.rpow_le_rpow_of_exponent_le hb hst)

theorem auxiliaryInflation_child_base_le (d L t : ℝ)
    (hd : 1 ≤ d) (hL : 0 < L) (ht : 1 < t) :
    (t - 1) ^ d / (L * ((t - 1) / t)) ≤ t ^ d / L := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  calc
    _ = (t / L) * (t - 1) ^ (d - 1) := by
      rw [Real.rpow_sub ht1, Real.rpow_one]
      field_simp
    _ ≤ (t / L) * t ^ (d - 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht1.le (by linarith) (by linarith)) (div_nonneg ht0.le hL.le)
    _ = t ^ d / L := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
      field_simp

theorem auxiliaryInflation_child_le (d D p : ℝ) (hd : 1 ≤ d)
    (hD : 1 < D) (hp : 1 < p) (hs : 1 < sieveParameter D p) :
    auxiliaryInflation d (D / p) (sieveParameter (D / p) p) ≤
      auxiliaryChildInflation d D (sieveParameter D p) := by
  rw [auxiliaryInflation, sieveParameter_div_self D p (by linarith) hp,
    log_child_level_eq D p hD hp]
  have hbase := auxiliaryInflation_child_base_le d (Real.log D) (sieveParameter D p)
    hd (Real.log_pos hD) hs
  apply Real.rpow_le_rpow _ (_root_.add_le_add le_rfl hbase) (by linarith)
  have ht0 : 0 < sieveParameter D p := by linarith
  have ht1 : 0 < sieveParameter D p - 1 := by linarith
  have hn := div_nonneg (Real.rpow_nonneg ht1.le d)
    (mul_nonneg (Real.log_pos hD).le (div_nonneg ht1.le ht0.le))
  linarith

theorem auxiliaryChildInflation_le (d D s : ℝ) (hD : 1 < D) (hs : 0 ≤ s) :
    auxiliaryChildInflation d D s ≤ auxiliaryInflation d D s := by
  apply Real.rpow_le_rpow_of_exponent_le _ (by linarith : s - 1 ≤ s)
  have := div_nonneg (Real.rpow_nonneg hs d) (Real.log_pos hD).le
  linarith

theorem tendsto_auxiliaryInflation_one (d s : ℝ) :
    Tendsto (fun D => auxiliaryInflation d D s) atTop (𝓝 1) := by
  have hq : Tendsto (fun D => s ^ d / Real.log D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hb := (tendsto_const_nhds (x := (1 : ℝ))).add hq
  have hr := hb.rpow_const (p := s) (Or.inl (by norm_num : (1 : ℝ) + 0 ≠ 0))
  simpa only [auxiliaryInflation, add_zero, Real.one_rpow] using hr

end Chen.LinearSieve
