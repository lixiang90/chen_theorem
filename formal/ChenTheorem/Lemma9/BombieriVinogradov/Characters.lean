import ChenTheorem.Lemma9.BombieriVinogradov.Basic
import ChenTheorem.Lemma5.Core
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Character reduction for Bombieri--Vinogradov

The progression error is first written exactly as an average of twisted
von-Mangoldt sums over all characters.  This finite identity is the bridge
between the progression statement and the primitive-character large sieve.
-/

/-- Subtract the expected main term from the principal character only. -/
noncomputable def adjustedTwistedPsi {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  twistedPsi x χ - if χ = 1 then (x : ℂ) else 0

/-- Exact character-orthogonality expansion of `ψ(x; q, a)`. -/
theorem progressionPsi_eq_character_average
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (progressionPsi x q a : ℂ) =
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
        (Nat.totient q : ℂ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (progressionPsi x q a : ℂ) =
        ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((if n ≡ a [MOD q] then 1 else 0 : ℝ) : ℂ)) := by
      rw [progressionPsi]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hna : n ≡ a [MOD q]
      · simp [hna]
      · simp [hna]
    _ = ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) /
              (Nat.totient q : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Chen.residueIndicator_eq_character_average
        (d := q) (x := a) (m := n) hq ha]
      by_cases hna : n ≡ a [MOD q]
      · rw [if_pos hna, if_pos hna.symm]
      · rw [if_neg hna, if_neg (fun han => hna han.symm)]
    _ = (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
        (Nat.totient q : ℂ) := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      calc
        ∑ n ∈ Finset.Icc 1 x,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              ∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ * χ (n : ZMod q) =
            ∑ n ∈ Finset.Icc 1 x,
              ∑ χ : DirichletCharacter ℂ q,
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ q,
              ∑ n ∈ Finset.Icc 1 x,
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) := by
              rw [Finset.sum_comm]
        _ = ∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ := by
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [twistedPsi, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              ring

/-- Exact character expansion after subtracting the expected principal main
term. -/
theorem progressionError_eq_adjusted_character_average
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (progressionPsi x q a : ℂ) -
        (x : ℂ) / (Nat.totient q : ℂ) =
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
        (Nat.totient q : ℂ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hainvunit : IsUnit ((a : ZMod q)⁻¹) := by
    have haunitInt : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast] using haunit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv haunitInt
  have hprincipal :
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ *
            (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    simp_rw [mul_ite, mul_zero]
    rw [Fintype.sum_ite_eq'
      (1 : DirichletCharacter ℂ q)
      (fun χ => χ (a : ZMod q)⁻¹ * (x : ℂ))]
    rw [MulChar.one_apply hainvunit, one_mul]
  rw [progressionPsi_eq_character_average hq ha]
  calc
    (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
          (Nat.totient q : ℂ) -
        (x : ℂ) / (Nat.totient q : ℂ) =
      ((∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) - (x : ℂ)) /
        (Nat.totient q : ℂ) := by ring
    _ = (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
        (Nat.totient q : ℂ) := by
      apply congrArg (fun z : ℂ => z / (Nat.totient q : ℂ))
      calc
        (∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ) - (x : ℂ) =
            (∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ) -
              ∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ *
                  (if χ = 1 then (x : ℂ) else 0) := by
              rw [hprincipal]
        _ = ∑ χ : DirichletCharacter ℂ q,
              (χ (a : ZMod q)⁻¹ * twistedPsi x χ -
                χ (a : ZMod q)⁻¹ *
                  (if χ = 1 then (x : ℂ) else 0)) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ := by
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [adjustedTwistedPsi]
              ring_nf

/-- A reduced progression error is bounded by the average of the adjusted
twisted sums over all characters modulo `q`. -/
theorem progressionError_le_sum_norm_adjustedTwistedPsi
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    progressionError x q a ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hφ : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hainvunit : IsUnit ((a : ZMod q)⁻¹) := by
    have haunitInt : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast] using haunit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv haunitInt
  have hcharNorm : ∀ χ : DirichletCharacter ℂ q,
      ‖χ (a : ZMod q)⁻¹‖ = 1 := by
    intro χ
    simpa only [IsUnit.unit_spec] using
      χ.unit_norm_eq_one hainvunit.unit
  have hsum :
      ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ ≤
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
    calc
      ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ‖χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ :=
        norm_sum_le _ _
      _ = ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [norm_mul, hcharNorm χ, one_mul]
  calc
    progressionError x q a =
        ‖(progressionPsi x q a : ℂ) -
          (x : ℂ) / (Nat.totient q : ℂ)‖ := by
      rw [progressionError]
      have hcast :
          ((progressionPsi x q a -
              (x : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) =
            (progressionPsi x q a : ℂ) -
              (x : ℂ) / (Nat.totient q : ℂ) := by
        push_cast
        ring
      rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
            (Nat.totient q : ℂ)‖ := by
      rw [progressionError_eq_adjusted_character_average hq ha]
    _ = ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ /
            (Nat.totient q : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
    _ ≤ (∑ χ : DirichletCharacter ℂ q,
          ‖adjustedTwistedPsi x χ‖) / (Nat.totient q : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hφ.le
    _ = (Nat.totient q : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by ring

/-- The same character bound, uniformly over the reduced residue classes. -/
theorem maxProgressionError_le_sum_norm_adjustedTwistedPsi
    {x q : ℕ} (hq : 0 < q) :
    maxProgressionError x q ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
  classical
  rw [maxProgressionError, dif_neg hq.ne']
  apply Finset.sup'_le
  intro a ha
  rw [reducedProgressionError]
  split_ifs with hac
  · exact progressionError_le_sum_norm_adjustedTwistedPsi hq hac
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun χ _ => norm_nonneg _)

/-- Finite character reduction of the averaged progression error. -/
theorem sum_maxProgressionError_le_character_sum (x Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        (Nat.totient q : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by
  apply Finset.sum_le_sum
  intro q hq
  exact maxProgressionError_le_sum_norm_adjustedTwistedPsi
    (Finset.mem_Icc.mp hq).1

end Chen.BombieriVinogradov
