import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthTail

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem primeDensityMass_le_neg_log_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) :
    primeDensityMass P z ≤ -Real.log (sieveProduct P primeDensity z) := by
  have hpos : ∀ p ∈ range z, 0 < 1 - if p ∈ P then primeDensity p else 0 := by
    intro p _
    split_ifs with hp
    · exact sub_pos.mpr (primeDensity_bounds (hP p hp) (hodd p hp)).2
    · norm_num
  have hlog : Real.log (sieveProduct P primeDensity z) =
      ∑ p ∈ range z, Real.log (1 - if p ∈ P then primeDensity p else 0) := by
    unfold sieveProduct
    exact Real.log_prod (fun p hp => (hpos p hp).ne')
  rw [hlog, ← sum_neg_distrib]
  apply sum_le_sum
  intro p hp
  have h := Real.log_le_sub_one_of_pos (hpos p hp)
  linarith

theorem primeDensity_sieveProduct_three (P : Finset ℕ) (hodd : ∀ p ∈ P, 2 < p) :
    sieveProduct P primeDensity 3 = 1 := by
  have h0 : 0 ∉ P := by intro hp; have := hodd 0 hp; omega
  have h1 : 1 ∉ P := by intro hp; have := hodd 1 hp; omega
  have h2 : 2 ∉ P := by intro hp; have := hodd 2 hp; omega
  norm_num [sieveProduct, prod_range_succ, h0, h1, h2]

/-- The unrestricted chain mass grows only on the log-log scale. The
same density constant controls its exponential, uniformly in `P`. -/
theorem primeDensityMass_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      primeDensityMass P (z + 1) ≤
        Real.log ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ∧
      Real.exp (primeDensityMass P (z + 1)) ≤
        (1 + K / Real.log 2) * (Real.log z / Real.log 2) ∧
      (sieveProduct P primeDensity (z + 1))⁻¹ ≤
        (1 + K / Real.log 2) * (Real.log z / Real.log 2) := by
  obtain ⟨K, hK, hb⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd
  have hratio := hb 2 z le_rfl hz P hP hodd
  rw [primeDensity_sieveProduct_three P hodd, one_div] at hratio
  norm_num only [Nat.cast_ofNat] at hratio
  have hprod := primeDensity_sieveProduct_pos P hP hodd (z + 1)
  have hpos : 0 < (1 + K / Real.log 2) * (Real.log z / Real.log 2) :=
    (inv_pos.mpr hprod).trans_le hratio
  have hlog := Real.log_le_log (inv_pos.mpr hprod) hratio
  rw [Real.log_inv] at hlog
  have hmass := (primeDensityMass_le_neg_log_product P hP hodd (z + 1)).trans hlog
  refine ⟨hmass, ?_, hratio⟩
  have h := Real.exp_le_exp.mpr hmass
  rwa [Real.exp_log hpos] at h

/-- An explicit depth-tail estimate using only the already proved
dimension-one constant and the cutoff, with no unknown prime-density sum. -/
theorem rosserDefect_partial_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ N : ℕ, ∀ upper : Bool, ∀ D : ℝ,
      rosserDefect P primeDensity (z + 1) upper D -
        (∑ n ∈ range N, rosserStoppingMass P n (z + 1) upper D) ≤
      (Real.log ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ^ N / N.factorial) *
        ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) := by
  obtain ⟨K, hK, hb⟩ := primeDensityMass_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd N upper D
  have hmass := primeDensityMass_nonneg P hP hodd (z + 1)
  obtain ⟨hlog, hexp, _⟩ := hb z hz P hP hodd
  have hlog0 := hmass.trans hlog
  apply (rosserDefect_partial_bounds P hP hodd N (z + 1) upper D).2.trans
  gcongr

end Chen.LinearSieve
