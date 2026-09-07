import Submission.ChenTheorem.Lemma9.LinearSieve.RosserFixedDepth

set_option autoImplicit true
open Finset Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The dimension-one majorant for both the exponential density mass
and the reciprocal sieve product. -/
noncomputable def depthMassMajorant (K z : ℝ) : ℝ :=
  (1 + K / Real.log 2) * (Real.log z / Real.log 2)

/-- Normalize the already proved factorial tail by the actual product.
The estimate is uniform in the level and applies to every depth cutoff. -/
theorem rosserRelativeDefect_partial_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ N : ℕ, ∀ upper : Bool, ∀ D : ℝ,
      0 ≤ rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range N, rosserRelativeStoppingMass P n (z + 1) upper D) ∧
      rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range N, rosserRelativeStoppingMass P n (z + 1) upper D) ≤
          depthMassMajorant K z ^ 2 * (Real.log (depthMassMajorant K z) ^ N / N.factorial) := by
  obtain ⟨K, hK, hb⟩ := primeDensityMass_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd N upper D
  obtain ⟨hlog, hexp, hinv⟩ := hb z hz P hP hodd
  change primeDensityMass P (z + 1) ≤ Real.log (depthMassMajorant K z) at hlog
  change Real.exp (primeDensityMass P (z + 1)) ≤ depthMassMajorant K z at hexp
  change (sieveProduct P primeDensity (z + 1))⁻¹ ≤ depthMassMajorant K z at hinv
  have hL := primeDensityMass_nonneg P hP hodd (z + 1)
  have hlog0 := hL.trans hlog
  have hV := primeDensity_sieveProduct_pos P hP hodd (z + 1)
  have hB : 0 ≤ depthMassMajorant K z := (Real.exp_pos _).le.trans hexp
  obtain ⟨hnonneg, htail⟩ := rosserDefect_partial_bounds P hP hodd N (z + 1) upper D
  have heq : rosserRelativeDefect P (z + 1) upper D -
      (∑ n ∈ range N, rosserRelativeStoppingMass P n (z + 1) upper D) =
      (rosserDefect P primeDensity (z + 1) upper D -
        (∑ n ∈ range N, rosserStoppingMass P n (z + 1) upper D)) *
          (sieveProduct P primeDensity (z + 1))⁻¹ := by
    unfold rosserRelativeDefect rosserRelativeStoppingMass
    rw [← sum_div, ← sub_div, div_eq_mul_inv]
  rw [heq]
  refine ⟨mul_nonneg hnonneg (inv_nonneg.mpr hV.le), ?_⟩
  calc
    _ ≤ ((primeDensityMass P (z + 1) ^ N / N.factorial) * Real.exp (primeDensityMass P (z + 1))) *
        (sieveProduct P primeDensity (z + 1))⁻¹ :=
      mul_le_mul_of_nonneg_right htail (inv_nonneg.mpr hV.le)
    _ ≤ (Real.log (depthMassMajorant K z) ^ N / N.factorial) *
        depthMassMajorant K z * depthMassMajorant K z := by gcongr
    _ = _ := by ring

/-- Exponential-series domination of one term, with a factor two
inserted to obtain geometric decay in the truncation depth. -/
theorem factorial_log_tail_le_geometric (B : ℝ) (hB : 1 ≤ B) (N : ℕ) :
    B ^ 2 * (Real.log B ^ N / N.factorial) ≤ B ^ 4 / (2 : ℝ) ^ N := by
  have hB0 : 0 < B := by linarith
  have hx : 0 ≤ Real.log B := Real.log_nonneg hB
  have h := Real.pow_div_factorial_le_exp (2 * Real.log B) (by positivity) N
  have he : Real.exp (2 * Real.log B) = B ^ 2 := by
    simpa using Real.exp_nat_mul (Real.log B) 2 |>.trans (by rw [Real.exp_log hB0])
  rw [he, mul_pow] at h
  have hterm : Real.log B ^ N / N.factorial ≤ B ^ 2 / (2 : ℝ) ^ N := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)).mpr
    calc
      _ = (2 ^ N * Real.log B ^ N) / N.factorial := by ring
      _ ≤ B ^ 2 := h
  calc
    _ ≤ B ^ 2 * (B ^ 2 / (2 : ℝ) ^ N) := mul_le_mul_of_nonneg_left hterm (sq_nonneg B)
    _ = _ := by ring

/-- A logarithmic depth suffices for an inverse-square normalized tail. -/
theorem factorial_log_tail_le_inv_square (B : ℝ) (hB : 1 ≤ B) (N : ℕ)
    (hN : 6 * Real.log B ≤ (N : ℝ) * Real.log 2) :
    B ^ 2 * (Real.log B ^ N / N.factorial) ≤ 1 / B ^ 2 := by
  have hB0 : 0 < B := by linarith
  have h := Real.exp_le_exp.mpr hN
  have heB : Real.exp (6 * Real.log B) = B ^ 6 := by
    simpa using Real.exp_nat_mul (Real.log B) 6 |>.trans (by rw [Real.exp_log hB0])
  rw [heB, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  apply (factorial_log_tail_le_geometric B hB N).trans
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ N) (pow_pos hB0 2)]
  nlinarith [show B ^ 4 * B ^ 2 = B ^ 6 by ring]

noncomputable def factorialTailDepth (B : ℝ) : ℕ := ⌈6 * Real.log B / Real.log 2⌉₊

theorem factorialTailDepth_bound (B : ℝ) :
    6 * Real.log B ≤ (factorialTailDepth B : ℝ) * Real.log 2 := by
  have h := Nat.le_ceil (6 * Real.log B / Real.log 2)
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h

theorem depthMassMajorant_ge_one (K : ℝ) (hK : 0 < K) (z : ℝ) (hz : 2 ≤ z) :
    1 ≤ depthMassMajorant K z := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hz
  have hratio : 1 ≤ Real.log z / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hlog)
  unfold depthMassMajorant
  nlinarith [div_pos hK hl2]

/-- A depth growing only as the logarithm of the log-scale majorant
controls the actual remaining Rosser defect, uniformly in every level. -/
theorem rosserRelativeDefect_growing_tail_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool, ∀ D : ℝ,
      0 ≤ rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range (factorialTailDepth (depthMassMajorant K z)),
          rosserRelativeStoppingMass P n (z + 1) upper D) ∧
      rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range (factorialTailDepth (depthMassMajorant K z)),
          rosserRelativeStoppingMass P n (z + 1) upper D) ≤ 1 / depthMassMajorant K z ^ 2 := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_partial_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd upper D
  obtain ⟨h0, h1⟩ := hb z hz P hP hodd (factorialTailDepth (depthMassMajorant K z)) upper D
  exact ⟨h0, h1.trans (factorial_log_tail_le_inv_square _
    (depthMassMajorant_ge_one K hK z (by exact_mod_cast hz)) _ (factorialTailDepth_bound _))⟩

theorem factorialTailDepth_cast_bounds (B : ℝ) (hB : 1 ≤ B) :
    6 * Real.log B / Real.log 2 ≤ (factorialTailDepth B : ℝ) ∧
      (factorialTailDepth B : ℝ) < 6 * Real.log B / Real.log 2 + 1 := by
  have hx : 0 ≤ 6 * Real.log B / Real.log 2 :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hB))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hx⟩

theorem depthMassMajorant_tendsto (K : ℝ) (hK : 0 < K) :
    Tendsto (fun z : ℕ => depthMassMajorant K z) atTop atTop := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (hlog.atTop_div_const hl2).const_mul_atTop (by positivity : 0 < 1 + K / Real.log 2)

theorem depthMassMajorant_inv_square_tendsto (K : ℝ) (hK : 0 < K) :
    Tendsto (fun z : ℕ => 1 / depthMassMajorant K z ^ 2) atTop (𝓝 0) := by
  have hpow := (tendsto_pow_atTop (n := 2) (by norm_num)).comp (depthMassMajorant_tendsto K hK)
  exact tendsto_const_nhds.div_atTop hpow

/-- The remaining depth tail tends uniformly to zero, including
uniformity in the level `D` and the finite prime set. The initial sum now
has a growing, rather than fixed, number of terms. -/
theorem eventually_rosserRelativeDefect_growing_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool, ∀ D : ℝ,
      0 ≤ rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range (factorialTailDepth (depthMassMajorant K z)),
          rosserRelativeStoppingMass P n (z + 1) upper D) ∧
      rosserRelativeDefect P (z + 1) upper D -
        (∑ n ∈ range (factorialTailDepth (depthMassMajorant K z)),
          rosserRelativeStoppingMass P n (z + 1) upper D) ≤ ε := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_growing_tail_bound
  refine ⟨K, hK, ?_⟩
  intro ε hε
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (depthMassMajorant_inv_square_tendsto K hK).eventually (gt_mem_nhds hε)] with z hz herr
  intro P hP hodd upper D
  obtain ⟨h0, h1⟩ := hb z hz P hP hodd upper D
  exact ⟨h0, h1.trans herr.le⟩

end Chen.LinearSieve
