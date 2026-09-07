import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedSieveNormalization
import Mathlib.Order.Filter.AtTopBot.Prod

set_option autoImplicit true

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

theorem primeDensity_bounds {p : ℕ} (hp : p.Prime) (hodd : 2 < p) :
    0 ≤ primeDensity p ∧ primeDensity p < 1 := by
  simp only [primeDensity_apply, Nat.totient_prime hp]
  constructor
  · positivity
  · apply inv_lt_one_of_one_lt₀
    exact_mod_cast (show 1 < p - 1 by omega)

/-- The density product over every odd prime up to the cutoff. This
dominates the inverse interval product for every reduced sieve family. -/
noncomputable def fullPrimeSieveProduct (y : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesLE y, (1 - primeDensity p)

theorem fullPrimeSieveProduct_pos (y : ℕ) : 0 < fullPrimeSieveProduct y := by
  apply prod_pos
  intro p hp
  exact sub_pos.mpr (primeDensity_bounds (oddPrimesLE_prime hp) (mem_filter.mp hp).2).2

theorem fullPrimeSieveProduct_eq (y : ℕ) : fullPrimeSieveProduct y = primeSieveProduct 1 y := by
  have hs : (oddPrimesLE y).filter (fun p => ¬p ∣ 1) = oddPrimesLE y := by
    apply filter_eq_self.mpr
    intro p hp hd
    have := Nat.le_of_dvd (show 0 < 1 by omega) hd
    have := (oddPrimesLE_prime hp).two_le
    omega
  unfold primeSieveProduct
  rw [hs]
  rfl

theorem fullPrimeSieveProduct_log_tendsto :
    Tendsto (fun y : ℕ => fullPrimeSieveProduct y * Real.log y) atTop
      (nhds (2 * Real.exp (-Real.eulerMascheroniConstant) * chenConst 1)) := by
  have h := (primeSieveProduct_fixed_log_normalized_tendsto 1 (by decide)
    id tendsto_id).mul_const (chenConst 1)
  apply h.congr'
  apply Eventually.of_forall
  intro y
  have hC : chenConst 1 ≠ 0 := ne_of_gt (twinConst_pos.trans_le (twinConst_le_chenConst 1))
  dsimp only [id_eq]
  rw [fullPrimeSieveProduct_eq]
  field_simp

/-- A finite inverse density product over the interval `(w,z]`. -/
noncomputable def sieveIntervalProduct (P : Finset ℕ) (w z : ℕ) : ℝ :=
  ∏ p ∈ P with w < p ∧ p ≤ z, (1 - primeDensity p)⁻¹

theorem oddPrimesLE_mono {w z : ℕ} (hwz : w ≤ z) : oddPrimesLE w ⊆ oddPrimesLE z := by
  intro p hp
  obtain ⟨hpw, hodd⟩ := mem_filter.mp hp
  obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hpw
  exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle.trans hwz, hprime⟩, hodd⟩

/-- Exact factorization at two cutoffs, before any asymptotic estimate. -/
theorem fullPrimeSieveProduct_interval (w z : ℕ) (hwz : w ≤ z) :
    sieveIntervalProduct (oddPrimesLE z) w z = fullPrimeSieveProduct w / fullPrimeSieveProduct z := by
  have hset : (oddPrimesLE z).filter (fun p => w < p ∧ p ≤ z) =
      oddPrimesLE z \ oddPrimesLE w := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpz, hpw, _⟩ := mem_filter.mp hp
      refine mem_sdiff.mpr ⟨hpz, fun h => ?_⟩
      have := (Nat.mem_primesLE.mp (mem_filter.mp h).1).1
      omega
    · intro hp
      obtain ⟨hpz, hpw⟩ := mem_sdiff.mp hp
      obtain ⟨hpz', hodd⟩ := mem_filter.mp hpz
      obtain ⟨hpzle, hprime⟩ := Nat.mem_primesLE.mp hpz'
      have hwp : w < p := by
        by_contra hwp
        exact hpw (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hprime⟩, hodd⟩)
      exact mem_filter.mpr ⟨hpz, hwp, hpzle⟩
  have hsplit : (∏ p ∈ oddPrimesLE z \ oddPrimesLE w, (1 - primeDensity p)) *
      fullPrimeSieveProduct w = fullPrimeSieveProduct z := prod_sdiff (oddPrimesLE_mono hwz)
  have hw0 := ne_of_gt (fullPrimeSieveProduct_pos w)
  unfold sieveIntervalProduct
  rw [hset, Finset.prod_inv_distrib]
  have hquot : (∏ p ∈ oddPrimesLE z \ oddPrimesLE w, (1 - primeDensity p)) =
      fullPrimeSieveProduct z / fullPrimeSieveProduct w := (eq_div_iff hw0).mpr hsplit
  rw [hquot, inv_div]

/-- Omitting primes can only decrease an inverse density product.
The resulting bound is independent of the omitted residue parameter. -/
theorem sieveIntervalProduct_le_full (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (w z : ℕ) :
    sieveIntervalProduct P w z ≤ sieveIntervalProduct (oddPrimesLE z) w z := by
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hpP, hpw, hpz⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpz, hP p hpP⟩, hodd p hpP⟩,
      hpw, hpz⟩
  · intro p hp
    have hb := primeDensity_bounds (hP p (mem_filter.mp hp).1) (hodd p (mem_filter.mp hp).1)
    exact inv_nonneg.mpr (sub_pos.mpr hb.2).le
  · intro p hp _
    have hpz := (mem_filter.mp hp).1
    have hb := primeDensity_bounds (oddPrimesLE_prime hpz) (mem_filter.mp hpz).2
    simpa only [one_div] using (one_le_div (sub_pos.mpr hb.2)).mpr (sub_le_self 1 hb.1)

/-- The normalized full-product ratios tend to one with both cutoffs
independently tending to infinity. This gives a uniform interval bound. -/
theorem fullPrimeSieveProduct_normalized_ratio_tendsto :
    Tendsto (fun wz : ℕ × ℕ =>
      (fullPrimeSieveProduct wz.1 * Real.log wz.1) /
        (fullPrimeSieveProduct wz.2 * Real.log wz.2)) atTop (nhds 1) := by
  have hf := fullPrimeSieveProduct_log_tendsto.comp
    (show Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop by
      rw [← prod_atTop_atTop_eq]; exact tendsto_fst)
  have hg := fullPrimeSieveProduct_log_tendsto.comp
    (show Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop by
      rw [← prod_atTop_atTop_eq]; exact tendsto_snd)
  have hC : 0 < 2 * Real.exp (-Real.eulerMascheroniConstant) * chenConst 1 := by
    have := twinConst_pos.trans_le (twinConst_le_chenConst 1)
    positivity
  have hr := hf.div hg (ne_of_gt hC)
  rw [div_self (ne_of_gt hC)] at hr
  exact hr.congr' (Eventually.of_forall (fun _ => rfl))

/-- The dimension-one interval condition, with an arbitrarily small
relative error, holds uniformly over every finite set of odd primes.
In particular it applies to both Chen residue families. -/
theorem eventually_sieveIntervalProduct_le (ε : ℝ) (hε : 0 < ε) :
    ∃ W : ℕ, 2 ≤ W ∧ ∀ w z : ℕ, W ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        sieveIntervalProduct P w z ≤ (1 + ε) * (Real.log z / Real.log w) := by
  have he := fullPrimeSieveProduct_normalized_ratio_tendsto.eventually
    (eventually_lt_nhds (show (1 : ℝ) < 1 + ε by linarith))
  obtain ⟨W, hW⟩ := eventually_atTop_prod_self.mp he
  refine ⟨max W 2, le_max_right _ _, ?_⟩
  intro w z hw hwz P hP hodd
  have hw2 : 2 ≤ w := (le_max_right W 2).trans hw
  have hz2 : 2 ≤ z := hw2.trans hwz
  have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hb := hW w z ((le_max_left W 2).trans hw) (((le_max_left W 2).trans hw).trans hwz)
  have hratio : fullPrimeSieveProduct w / fullPrimeSieveProduct z ≤
      (1 + ε) * (Real.log z / Real.log w) := by
    have heq : fullPrimeSieveProduct w / fullPrimeSieveProduct z =
        ((fullPrimeSieveProduct w * Real.log w) / (fullPrimeSieveProduct z * Real.log z)) *
          (Real.log z / Real.log w) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hb.le (div_pos hlz hlw).le
  exact (sieveIntervalProduct_le_full P hP hodd w z).trans
    ((fullPrimeSieveProduct_interval w z hwz) ▸ hratio)

end Chen.LinearSieve
