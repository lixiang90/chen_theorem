import ChenTheorem.Lemma9.LinearSieve.RosserCubeCutoff

namespace Chen.LinearSieve

theorem strictAntiOn_sieveParameter {D : ℝ} (hD : 1 < D) :
    StrictAntiOn (sieveParameter D) (Set.Ioi 1) := by
  intro p hp z hz hpz
  exact div_lt_div_of_pos_left (Real.log_pos hD) (Real.log_pos hp)
    (Real.log_lt_log (by linarith [show 1 < p from hp]) hpz)

theorem child_level_gt_one {D p : ℝ} (hD : 1 < D) (hp : 1 < p)
    (hs : 1 < sieveParameter D p) : 1 < D / p := by
  have hlog := (lt_div_iff₀ (Real.log_pos hp)).mp hs
  have hlt : p < D := (Real.log_lt_log_iff (by linarith) (by linarith)).mp (by simpa using hlog)
  exact (lt_div_iff₀ (by linarith : 0 < p)).mpr (by simpa using hlt)

theorem rosserCubeCutoff_le_of_actual_parameter (D : ℝ) (hD : 1 < D)
    (hm : 2 ≤ rosserCubeCutoff D) (z : ℕ) (hz : 2 ≤ z)
    (hs : sieveParameter D (z + 1) ≤ 3) : rosserCubeCutoff D ≤ z := by
  have ht := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  by_contra h
  have hzm : z + 1 ≤ rosserCubeCutoff D := by omega
  have ha := sieveParameter_antitone hD (show 1 < (z : ℝ) + 1 by linarith) hmR
    (show (z : ℝ) + 1 ≤ rosserCubeCutoff D by exact_mod_cast hzm)
  linarith

end Chen.LinearSieve
