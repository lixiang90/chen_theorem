import ChenTheorem.Lemma7.Core
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Filter Real
open scoped Classical

namespace Chen

/-! # Positivity of Chen's singular series -/

noncomputable def twinFactorIncrement (p : Nat.Primes) : ℝ :=
  if 2 < (p : ℕ) then
    - (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) else 0

noncomputable def twinLocalFactor (p : Nat.Primes) : ℝ :=
  1 + twinFactorIncrement p

noncomputable def twinEulerFactor (p : Nat.Primes) : ℝ :=
  (twinLocalFactor p)⁻¹

theorem norm_twinFactorIncrement_le (p : Nat.Primes) :
    ‖twinFactorIncrement p‖ ≤
      4 * ((((p : ℕ) : ℝ) ^ 2)⁻¹) := by
  unfold twinFactorIncrement
  split_ifs with hp
  · let P : ℝ := ((p : ℕ) : ℝ)
    change ‖-1 / (P - 1) ^ 2‖ ≤ 4 * (P ^ 2)⁻¹
    have hpR : (2 : ℝ) < P := by
      dsimp only [P]
      exact_mod_cast hp
    have hp0 : (0 : ℝ) < P := by linarith
    have hd0 : (0 : ℝ) < (P - 1) ^ 2 :=
      pow_pos (by linarith) _
    have hp2 : (0 : ℝ) < P ^ 2 := pow_pos hp0 _
    have hprod : 0 ≤ (P - 2) * (3 * P - 2) :=
      mul_nonneg (by linarith) (by linarith)
    simp only [norm_div, norm_neg, norm_one, Real.norm_eq_abs,
      abs_pow, abs_of_pos (by linarith : 0 < P - 1)]
    change (1 : ℝ) / ((P - 1) ^ 2) ≤ 4 / (P ^ 2)
    exact (div_le_div_iff₀ hd0 hp2).2 (by nlinarith)
  · simp

theorem summable_norm_twinFactorIncrement :
    Summable (fun p : Nat.Primes => ‖twinFactorIncrement p‖) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    simpa [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hsub : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    hbase.subtype Nat.Prime
  refine (hsub.mul_left 4).of_nonneg_of_le (fun p => norm_nonneg _) ?_
  exact norm_twinFactorIncrement_le

theorem multipliable_twinLocalFactor : Multipliable twinLocalFactor := by
  exact multipliable_one_add_of_summable summable_norm_twinFactorIncrement

theorem twinConst_eq_tprod_twinLocalFactor :
    twinConst = ∏' p : Nat.Primes, twinLocalFactor p := by
  apply tprod_congr
  intro p
  unfold twinLocalFactor twinFactorIncrement
  split_ifs with hp
  · ring
  · ring

theorem twinEulerFactor_eq_inv_twinLocalFactor (p : Nat.Primes) :
    twinEulerFactor p = (twinLocalFactor p)⁻¹ := rfl

theorem twinEulerFactor_eq_formula (p : Nat.Primes) :
    twinEulerFactor p =
      if 2 < (p : ℕ) then
        1 + (1 : ℝ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2))
      else 1 := by
  unfold twinEulerFactor twinLocalFactor twinFactorIncrement
  split_ifs with hp
  · let P : ℝ := ((p : ℕ) : ℝ)
    change (1 + -1 / (P - 1) ^ 2)⁻¹ =
      1 + 1 / (P * (P - 2))
    have hpR : (2 : ℝ) < P := by
      dsimp only [P]
      exact_mod_cast hp
    have hp1 : P - 1 ≠ 0 := by linarith
    have hp2 : P - 2 ≠ 0 := by linarith
    have hp0 : P ≠ 0 := by linarith
    have hprod0 : P * (P - 2) ≠ 0 := mul_ne_zero hp0 hp2
    have hleft :
        1 + 1 / (P * (P - 2)) =
          (P - 1) ^ 2 / (P * (P - 2)) := by
      field_simp [hprod0]
      ring
    have hright :
        1 + -1 / (P - 1) ^ 2 =
          P * (P - 2) / (P - 1) ^ 2 := by
      field_simp [hp1]
      ring
    rw [hleft, hright, inv_div]
  · simp

/-- The twin-prime constant is positive. -/
theorem twinConst_pos : 0 < twinConst := by
  let a : Nat.Primes → ℝ := fun p =>
    if 2 < (p : ℕ) then
      - (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) else 0
  have ha_summable : Summable (fun p => ‖a p‖) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
      simpa [one_div] using
        (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    have hsub : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
      hbase.subtype Nat.Prime
    refine (hsub.mul_left 4).of_nonneg_of_le (fun p => norm_nonneg _) ?_
    intro p
    change ‖twinFactorIncrement p‖ ≤
      4 * ((((p : ℕ) : ℝ) ^ 2)⁻¹)
    exact norm_twinFactorIncrement_le p
  have hfac : ∀ p, 1 + a p ≠ 0 := by
    intro p
    dsimp only [a]
    split_ifs with hp
    · let P : ℝ := ((p : ℕ) : ℝ)
      change 1 + -1 / (P - 1) ^ 2 ≠ 0
      have hpR : (3 : ℝ) ≤ P := by
        dsimp only [P]
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have hden : (1 : ℝ) < (P - 1) ^ 2 := by
        nlinarith [sq_nonneg (P - 1)]
      have hinv : (1 : ℝ) / (P - 1) ^ 2 < 1 := by
        exact (div_lt_one (by positivity)).2 hden
      rw [neg_div]
      linarith
    · simp
  have hne : (∏' p : Nat.Primes, (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hfac ha_summable
  have hmult : Multipliable (fun p : Nat.Primes => 1 + a p) :=
    multipliable_one_add_of_summable ha_summable
  have hnonneg : 0 ≤ ∏' p : Nat.Primes, (1 + a p) := by
    apply le_hasProd_of_le_prod hmult.hasProd
    intro s
    apply Finset.prod_nonneg
    intro p hp
    dsimp only [a]
    split_ifs with hprime
    · let P : ℝ := ((p : ℕ) : ℝ)
      change 0 ≤ 1 + -1 / (P - 1) ^ 2
      have hpR : (3 : ℝ) ≤ P := by
        dsimp only [P]
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have hden : (1 : ℝ) ≤ (P - 1) ^ 2 := by
        nlinarith [sq_nonneg (P - 1)]
      have hinv : (1 : ℝ) / (P - 1) ^ 2 ≤ 1 := by
        exact (div_le_one (by positivity)).2 hden
      rw [neg_div]
      linarith
    · simp
  have heq : twinConst = ∏' p : Nat.Primes, (1 + a p) := by
    apply tprod_congr
    intro p
    dsimp only [a]
    split_ifs with hp
    · ring
    · ring
  rw [heq]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem hasProd_twinEulerFactor :
    HasProd twinEulerFactor twinConst⁻¹ := by
  rw [twinConst_eq_tprod_twinLocalFactor]
  unfold twinEulerFactor HasProd
  have hlocal := multipliable_twinLocalFactor.hasProd
  rw [HasProd] at hlocal
  have hne : (∏' p : Nat.Primes, twinLocalFactor p) ≠ 0 := by
    rw [← twinConst_eq_tprod_twinLocalFactor]
    exact twinConst_pos.ne'
  simpa only [Finset.prod_inv_distrib] using hlocal.inv₀ hne

/-- `C_x ≥ ∏_{p>2} (1 - 1/(p-1)²)`. -/
theorem twinConst_le_chenConst (x : ℕ) : twinConst ≤ chenConst x := by
  rw [chenConst]
  have hprod :
      1 ≤ ∏ p ∈ x.primeFactors.filter (2 < ·),
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    apply Finset.one_le_prod
    intro p hp
    have hp2 : 2 < p := (Finset.mem_filter.mp hp).2
    have hpR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
    have hden : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    apply (le_div_iff₀ hden).2
    linarith
  nlinarith [twinConst_pos]

/-- Finite odd-prime Euler products approximate `twinConst⁻¹` from
below to arbitrary prescribed accuracy after multiplication by
`twinConst`. -/
theorem exists_finiteEulerProduct_ge_one_sub
    {η : ℝ} (hη : 0 < η) :
    ∃ s : Finset ℕ,
      (∀ p ∈ s, p.Prime) ∧
      (∀ p ∈ s, 2 < p) ∧
      1 - η ≤ twinConst *
        ∏ p ∈ s,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have hthreshold :
      twinConst⁻¹ - η / twinConst < twinConst⁻¹ := by
    have : 0 < η / twinConst := div_pos hη twinConst_pos
    linarith
  have hevent :
      ∀ᶠ t : Finset Nat.Primes in atTop,
        twinConst⁻¹ - η / twinConst <
          ∏ p ∈ t, twinEulerFactor p :=
    hasProd_twinEulerFactor.eventually_const_lt hthreshold
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  let u : Finset Nat.Primes := t.filter (fun p => 2 < (p : ℕ))
  let s : Finset ℕ := u.image (fun p : Nat.Primes => (p : ℕ))
  have hpartial :
      twinConst⁻¹ - η / twinConst <
        ∏ p ∈ t, twinEulerFactor p := ht t (by rfl)
  have hfilter :
      (∏ p ∈ t, twinEulerFactor p) =
        ∏ p ∈ u, twinEulerFactor p := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hpt hpu
    have hpnot : ¬2 < (p : ℕ) := by
      intro hp
      exact hpu (Finset.mem_filter.mpr ⟨hpt, hp⟩)
    simp [twinEulerFactor, twinLocalFactor, twinFactorIncrement, hpnot]
  have hprod :
      (∏ p ∈ s,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) =
        ∏ p ∈ u, twinEulerFactor p := by
    unfold s
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro p hp
      have hp2 : 2 < (p : ℕ) := (Finset.mem_filter.mp hp).2
      rw [twinEulerFactor_eq_formula]
      simp [hp2]
    · intro p hp q hq hpq
      exact Subtype.ext hpq
  refine ⟨s, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hqu, rfl⟩
    exact q.property
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hqu, rfl⟩
    exact (Finset.mem_filter.mp hqu).2
  · rw [hprod, ← hfilter]
    have hmul := mul_lt_mul_of_pos_left hpartial twinConst_pos
    have htwin0 : twinConst ≠ 0 := twinConst_pos.ne'
    have hsimplify :
        twinConst * (twinConst⁻¹ - η / twinConst) = 1 - η := by
      field_simp
    rw [hsimplify] at hmul
    exact hmul.le

end Chen
