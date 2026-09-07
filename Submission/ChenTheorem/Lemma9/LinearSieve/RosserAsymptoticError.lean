import Submission.ChenTheorem.Lemma9.LinearSieve.RosserUniformError

set_option autoImplicit true
open Filter Set
open scoped Topology

namespace Chen.LinearSieve

theorem eventually_inflatedError_compact_small (d δ a b ε : ℝ) (H : ℝ → ℝ)
    (hd : 0 ≤ d) (hδ : 0 < δ) (ha : 1 < a) (hab : a ≤ b) (hε : 0 < ε)
    (hH : 0 ≤ H a) (hanti : AntitoneOn H (Ioi 1)) :
    ∀ᶠ D : ℝ in atTop, ∀ s : ℝ, a ≤ s → s ≤ b → inflatedAuxiliaryError d δ D s H ≤ ε := by
  filter_upwards [(tendsto_inflatedAuxiliaryError_zero d δ b (fun _ => H a) hδ).eventually (gt_mem_nhds hε),
    eventually_gt_atTop (1 : ℝ)] with D hεD hD
  intro s has hsb
  have hs : 1 < s := ha.trans_le has
  have hsbH : s * H s ≤ b * H a :=
    (mul_le_mul_of_nonneg_left (hanti ha hs has) (by linarith : 0 ≤ s)).trans
      (mul_le_mul_of_nonneg_right hsb hH)
  have hi := monotoneOn_auxiliaryInflation d D hd hD
    (show 0 ≤ s by linarith) (show 0 ≤ b by linarith) hsb
  have hpow := Real.rpow_nonneg (Real.log_pos hD).le (-δ)
  have hfirst := mul_le_mul_of_nonneg_left hsbH
    (mul_nonneg (auxiliaryInflation_pos d D s hD (by linarith)).le hpow)
  have hsecond := mul_le_mul_of_nonneg_right hi
    (mul_nonneg hpow (mul_nonneg (show 0 ≤ b by linarith) hH))
  have he : inflatedAuxiliaryError d δ D s H ≤ inflatedAuxiliaryError d δ D b (fun _ => H a) := by
    unfold inflatedAuxiliaryError auxiliaryErrorScale
    calc
      _ ≤ auxiliaryInflation d D s * ((Real.log D) ^ (-δ) * (b * H a)) := by
        convert! hfirst using 1 <;> ring
      _ ≤ _ := by convert! hsecond using 1; ring
  exact he.trans hεD.le

/-- Actual upper Rosser defects approach the constructed upper error
uniformly on every compact parameter interval above one. -/
theorem eventually_rosser_upper_error_compact (a b ε : ℝ) (ha : 1 < a)
    (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D (z + 1)) + ε := by
  obtain ⟨M, hM, hb⟩ := rosserRelativeDefect_uniform_error 8 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hM0 : 0 < M := by linarith
  filter_upwards [eventually_inflatedError_compact_small 8 (1 / 2) a b (ε / M) upperAuxiliaryError
    (by norm_num) (by norm_num) ha hab (div_pos hε hM0) (upperAuxiliaryError_nonneg a ha) antitoneOn_upperAuxiliaryError,
    eventually_gt_atTop (1 : ℝ)] with D he hD
  intro z hz has hsb P hP hodd
  have h := (hb P hP hodd z hz D hD).1 (ha.trans_le has)
  have hm := mul_le_mul_of_nonneg_left (he _ has hsb) hM0.le
  rw [mul_div_cancel₀ _ hM0.ne'] at hm
  exact h.trans (_root_.add_le_add le_rfl hm)

theorem eventually_rosser_lower_error_compact (a b ε : ℝ) (ha : 2 < a)
    (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeDefect P (z + 1) false D ≤ lowerContinuousError (sieveParameter D (z + 1)) + ε := by
  obtain ⟨M, hM, hb⟩ := rosserRelativeDefect_uniform_error 8 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hM0 : 0 < M := by linarith
  have hanti : AntitoneOn lowerAuxiliaryError (Ioi 1) := antitoneOn_lowerAuxiliaryError.mono (by
    intro s hs; change 0 < s; linarith [show 1 < s from hs])
  filter_upwards [eventually_inflatedError_compact_small 8 (1 / 2) a b (ε / M) lowerAuxiliaryError
    (by norm_num) (by norm_num) (by linarith) hab (div_pos hε hM0) (lowerAuxiliaryError_nonneg a (by linarith)) hanti,
    eventually_gt_atTop (1 : ℝ)] with D he hD
  intro z hz has hsb P hP hodd
  have h := (hb P hP hodd z hz D hD).2 (ha.trans_le has)
  have hm := mul_le_mul_of_nonneg_left (he _ has hsb) hM0.le
  rw [mul_div_cancel₀ _ hM0.ne'] at hm
  exact h.trans (_root_.add_le_add le_rfl hm)

/-- The upper polynomial bound is unconditional for the constructed sieve
function; identifying its initial constant with 2 exp gamma is separate. -/
theorem eventually_rosser_upper_polynomial_compact (a b ε : ℝ) (ha : 1 < a)
    (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserEval P primeDensity (z + 1) true D ≤
        sieveProduct P primeDensity (z + 1) * (upperLinearSieveFunction (sieveParameter D (z + 1)) + ε) := by
  filter_upwards [eventually_rosser_upper_error_compact a b ε ha hab hε] with D hb
  intro z hz has hsb P hP hodd
  rw [(rosserEval_eq_product_mul_relativeDefect P hP hodd (z + 1) D).2]
  apply mul_le_mul_of_nonneg_left _ (primeDensity_sieveProduct_pos P hP hodd _).le
  have h := hb z hz has hsb P hP hodd
  unfold upperLinearSieveFunction
  linarith

theorem eventually_rosser_lower_polynomial_compact (a b ε : ℝ) (ha : 2 < a)
    (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      sieveProduct P primeDensity (z + 1) * (lowerLinearSieveFunction (sieveParameter D (z + 1)) - ε) ≤
        rosserEval P primeDensity (z + 1) false D := by
  filter_upwards [eventually_rosser_lower_error_compact a b ε ha hab hε] with D hb
  intro z hz has hsb P hP hodd
  rw [(rosserEval_eq_product_mul_relativeDefect P hP hodd (z + 1) D).1]
  apply mul_le_mul_of_nonneg_left _ (primeDensity_sieveProduct_pos P hP hodd _).le
  have h := hb z hz has hsb P hP hodd
  unfold lowerLinearSieveFunction
  linarith

end Chen.LinearSieve
