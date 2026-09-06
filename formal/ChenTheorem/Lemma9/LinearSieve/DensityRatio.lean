import ChenTheorem.Lemma9.LinearSieve.DensityInterval

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

/-- The recursive product ignores prime-set entries beyond its exclusive
cutoff. This form also applies inside a Rosser recursion branch. -/
theorem sieveProduct_eq_filtered_prod (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) :
    sieveProduct P g z = ∏ p ∈ P with p < z, (1 - g p) := by
  have hs : (range z).filter (fun p => p ∈ P) = P.filter (fun p => p < z) := by
    apply Finset.ext
    intro p
    simp only [mem_filter, mem_range, and_comm]
  unfold sieveProduct
  calc
    _ = ∏ p ∈ range z, (if p ∈ P then 1 - g p else 1) := by
      apply prod_congr rfl
      intro p _
      split_ifs <;> simp
    _ = ∏ p ∈ range z with p ∈ P, (1 - g p) := (prod_filter _ _).symm
    _ = _ := by rw [hs]

theorem primeDensity_sieveProduct_pos (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) :
    0 < sieveProduct P primeDensity z := by
  rw [sieveProduct_eq_filtered_prod]
  apply prod_pos
  intro p hp
  exact sub_pos.mpr (primeDensity_bounds (hP p (mem_filter.mp hp).1)
    (hodd p (mem_filter.mp hp).1)).2

/-- The exact ratio needed in normalized Buchstab/Rosser recursions. -/
theorem primeDensity_sieveProduct_ratio (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (w z : ℕ) (hwz : w ≤ z) :
    sieveProduct P primeDensity (w + 1) / sieveProduct P primeDensity (z + 1) =
      sieveIntervalProduct P w z := by
  have hsub : P.filter (fun p => p ≤ w) ⊆ P.filter (fun p => p ≤ z) := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.trans hwz⟩
  have hs : (P.filter (fun p => p ≤ z)) \ (P.filter (fun p => p ≤ w)) =
      P.filter (fun p => w < p ∧ p ≤ z) := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨hpz, hpw⟩ := mem_sdiff.mp hp
      have hpP := (mem_filter.mp hpz).1
      have hpzle := (mem_filter.mp hpz).2
      have hwp : w < p := by
        by_contra hwp
        exact hpw (mem_filter.mpr ⟨hpP, by omega⟩)
      exact mem_filter.mpr ⟨hpP, hwp, hpzle⟩
    · intro hp
      obtain ⟨hpP, hwp, hpz⟩ := mem_filter.mp hp
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hpP, hpz⟩, fun hpw => ?_⟩
      have := (mem_filter.mp hpw).2
      omega
  have hsplit := prod_sdiff (f := fun p => 1 - primeDensity p) hsub
  rw [hs] at hsplit
  have hw0 : (∏ p ∈ P with p ≤ w, (1 - primeDensity p)) ≠ 0 := by
    simpa only [sieveProduct_eq_filtered_prod, Nat.lt_succ_iff] using
      ne_of_gt (primeDensity_sieveProduct_pos P hP hodd (w + 1))
  have hquot := (eq_div_iff hw0).mpr hsplit
  simp only [sieveProduct_eq_filtered_prod, Nat.lt_succ_iff]
  unfold sieveIntervalProduct
  rw [prod_inv_distrib, hquot, inv_div]

/-- A uniform dimension-one bound for the exact products appearing in
the constructed sieve. No additional analytic density hypothesis is
assumed for either of Chen's residue families. -/
theorem eventually_primeDensity_sieveProduct_ratio_le (ε : ℝ) (hε : 0 < ε) :
    ∃ W : ℕ, 2 ≤ W ∧ ∀ w z : ℕ, W ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        sieveProduct P primeDensity (w + 1) / sieveProduct P primeDensity (z + 1) ≤
          (1 + ε) * (Real.log z / Real.log w) := by
  obtain ⟨W, hW2, hW⟩ := eventually_sieveIntervalProduct_le ε hε
  refine ⟨W, hW2, fun w z hw hwz P hP hodd => ?_⟩
  rw [primeDensity_sieveProduct_ratio P hP hodd w z hwz]
  exact hW w z hw hwz P hP hodd

end Chen.LinearSieve
