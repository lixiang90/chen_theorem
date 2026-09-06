import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryTransport
import ChenTheorem.Lemma9.LinearSieve.RosserGrowingPrefix

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem growingPrefix_bound_transport (C σ s t e Es Et p : ℝ)
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hs : 0 < s) (ht : 0 < t)
    (hσt : σ ≤ t) (he : 0 ≤ e) (hEs : 0 ≤ Es)
    (hp : p ≤ (C * σ / s) * e * Et) (hEt : Et ≤ (s / t) * Es) :
    p ≤ C * e * Es := by
  have hmul := mul_le_mul_of_nonneg_left hEt
    (mul_nonneg (div_nonneg (mul_nonneg hC hσ) hs.le) he)
  have hr : σ / t ≤ 1 := (div_le_one ht).mpr hσt
  have hlast := mul_le_mul_of_nonneg_right hr (mul_nonneg (mul_nonneg hC he) hEs)
  calc
    p ≤ (C * σ / s) * e * Et := hp
    _ ≤ (C * σ / s) * e * ((s / t) * Es) := hmul
    _ = (σ / t) * (C * e * Es) := by field_simp
    _ ≤ C * e * Es := by simpa only [one_mul] using hlast

/-- The actual small-prime prefix, uniformly in its cumulative depth, is
exponentially small relative to the auxiliary error at the parent parameter. -/
theorem rosserPartialPrefix_parent_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d δ : ℝ, 2 < d → ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → 3 ≤ sieveParameter D (z + 1) →
      ∀ upper : Bool,
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        C * Real.exp (-growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) ∧
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        C * Real.exp (-growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  obtain ⟨K, hK, hpref⟩ := rosserPartialPrefix_growing_uniform_bound
  let C := 4 * (1 + K / Real.log 2)
  have hC : 0 < C := by
    dsimp [C]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨C, hC, ?_⟩
  intro d δ hd
  filter_upwards [hpref d δ hd, eventually_inflatedAuxiliaryError_transport d δ (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hp htrans hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro P hP hodd N z hmz hs upper
  have hst : sieveParameter D (z + 1) ≤ sieveParameter D (growingPrefixIndex d D + 1) := by
    apply sieveParameter_antitone hD
    · change 1 < (growingPrefixIndex d D : ℝ) + 1
      exact_mod_cast (show 1 < growingPrefixIndex d D + 1 by omega)
    · change 1 < (z : ℝ) + 1
      exact_mod_cast (show 1 < z + 1 by omega)
    · exact_mod_cast Nat.add_le_add_right hmz 1
  have ht0 : 0 < sieveParameter D (growingPrefixIndex d D + 1) := by linarith
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).le
  have hb := hp P hP hodd N z hmz upper
  have ht := htrans.2 _ _ hs hst hhi
  have hstep : ∀ H : ℝ → ℝ, 0 ≤ H (sieveParameter D (z + 1)) →
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (C * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) H →
      inflatedAuxiliaryError d δ D (sieveParameter D (growingPrefixIndex d D + 1)) H ≤
        (sieveParameter D (z + 1) / sieveParameter D (growingPrefixIndex d D + 1)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) H →
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        C * Real.exp (-growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) H := by
    intro H hH hb ht
    exact growingPrefix_bound_transport _ _ _ _ _ _ _ _ hC.le hσ (by linarith) ht0 hlo
      (Real.exp_pos _).le (inflatedAuxiliaryError_nonneg d δ D _ H hD (by linarith) hH) hb ht
  exact ⟨hstep upperAuxiliaryError (upperAuxiliaryError_nonneg _ (by linarith)) hb.1 ht.1,
    hstep lowerAuxiliaryError (lowerAuxiliaryError_nonneg _ (by linarith)) hb.2 ht.2⟩

/-- The prefix consumes an arbitrarily small fixed fraction of the parent
error, with a level threshold independent of the depth and prime set. -/
theorem rosserPartialPrefix_parent_small (d δ ε : ℝ) (hd : 2 < d) (hε : 0 < ε) :
    ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → 3 ≤ sieveParameter D (z + 1) →
      ∀ upper : Bool,
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        ε * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) ∧
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        ε * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  obtain ⟨C, _, hC⟩ := rosserPartialPrefix_parent_bound
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hg).const_mul C
  simp only [mul_zero] at he
  filter_upwards [hC d δ hd, he.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)]
    with D hb he hD
  dsimp only [Function.comp_def] at he
  intro P hP hodd N z hmz hs upper
  have h := hb P hP hodd N z hmz hs upper
  have hu := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) upperAuxiliaryError hD (by linarith)
    (upperAuxiliaryError_nonneg _ (by linarith))
  have hl := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError hD (by linarith)
    (lowerAuxiliaryError_nonneg _ (by linarith))
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right he.le hu),
    h.2.trans (mul_le_mul_of_nonneg_right he.le hl)⟩

end Chen.LinearSieve
