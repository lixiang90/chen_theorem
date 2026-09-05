import ChenTheorem.Lemma9.BombieriVinogradov.TypeII
import ChenTheorem.Lemma9.BombieriVinogradov.MeanValue

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Reindexing by primitive conductor

The character-orthogonality reduction initially sums over every character
at every ambient modulus.  This file performs the exact, lossless reindexing
by the conductor and its primitive character.  Bounding the discrepancy
between a lift and its primitive source is the next arithmetic step.
-/

/-- Reindex a real-valued character sum by primitive conductor. -/
theorem sum_characters_real_eq_sum_primitiveLifts
    (q : ℕ) [NeZero q] (F : DirichletCharacter ℂ q → ℝ) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      ∑ z : Σ k : ↥q.divisors,
        {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          F (Chen.primitiveLift q z) :=
  ((Chen.primitiveLiftEquiv q).sum_comp F).symm

/-- Exact conductor partition of the adjusted twisted-character norm. -/
theorem sum_norm_adjustedTwistedPsi_eq_primitiveLifts
    (x q : ℕ) [NeZero q] :
    (∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖) =
      ∑ z : Σ k : ↥q.divisors,
        {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          ‖adjustedTwistedPsi x (Chen.primitiveLift q z)‖ :=
  sum_characters_real_eq_sum_primitiveLifts q
    (fun χ => ‖adjustedTwistedPsi x χ‖)

/-- A lifted primitive character agrees with its source away from the prime
divisors introduced by the ambient modulus. -/
theorem primitiveLift_apply_of_coprime
    (q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive})
    (n : ℕ) (hn : n.Coprime q) :
    Chen.primitiveLift q z n = z.2.1 n := by
  obtain ⟨k, ψ⟩ := z
  change DirichletCharacter.changeLevel
      (Nat.dvd_of_mem_divisors k.2) ψ.1 n = ψ.1 n
  have hn' : IsCoprime (n : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hn
  simpa only [Int.cast_natCast] using
    (DirichletCharacter.changeLevel_eq_cast_of_dvd'
      ψ.1 (Nat.dvd_of_mem_divisors k.2) hn')

/-- A primitive lift is principal exactly when its primitive source is
principal. -/
theorem primitiveLift_eq_one_iff
    (q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive}) :
    Chen.primitiveLift q z = 1 ↔ z.2.1 = 1 := by
  obtain ⟨k, ψ⟩ := z
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2) (NeZero.pos q)).ne'⟩
  change DirichletCharacter.changeLevel
      (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1 ↔ ψ.1 = 1
  exact DirichletCharacter.changeLevel_eq_one_iff
    (χ := ψ.1) (Nat.dvd_of_mem_divisors k.2)

/-- The imprimitive twisting discrepancy is supported on integers sharing a
prime factor with the ambient modulus. -/
theorem twistedPsi_primitiveLift_sub_eq_bad_sum
    (x q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive}) :
    twistedPsi x (Chen.primitiveLift q z) - twistedPsi x z.2.1 =
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Chen.primitiveLift q z n - z.2.1 n) := by
  rw [twistedPsi, twistedPsi, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · rw [if_neg (not_not.mpr hcop), primitiveLift_apply_of_coprime q z n hcop,
      sub_self, mul_zero]
  · rw [if_pos hcop]

/-- The principal-character adjustment is unchanged by passage between a
primitive source and its lift. -/
theorem adjustedTwistedPsi_primitiveLift_sub
    (x q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive}) :
    adjustedTwistedPsi x (Chen.primitiveLift q z) -
        adjustedTwistedPsi x z.2.1 =
      twistedPsi x (Chen.primitiveLift q z) - twistedPsi x z.2.1 := by
  rw [adjustedTwistedPsi, adjustedTwistedPsi]
  have hone : Chen.primitiveLift q z = 1 ↔ z.2.1 = 1 :=
    primitiveLift_eq_one_iff q z
  by_cases h : Chen.primitiveLift q z = 1
  · rw [if_pos h, if_pos (hone.mp h)]
    ring
  · rw [if_neg h, if_neg (hone.not.mp h)]
    ring

/-- Totalized conductor partition at one ambient modulus. -/
noncomputable def primitiveLiftAdjustedNormSum (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
        ‖adjustedTwistedPsi x (Chen.primitiveLift q z)‖

theorem sum_norm_adjustedTwistedPsi_eq_primitiveLiftAdjustedNormSum
    (x q : ℕ) [NeZero q] :
    (∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖) =
      primitiveLiftAdjustedNormSum x q := by
  rw [sum_norm_adjustedTwistedPsi_eq_primitiveLifts,
    primitiveLiftAdjustedNormSum, dif_neg (NeZero.ne q)]

/-- The full character majorant for progressions, before grouping equal
primitive conductors across ambient moduli. -/
noncomputable def allCharacterMean (x Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖

/-- Exact replacement of every ambient character by its primitive lift. -/
theorem allCharacterMean_eq_primitiveLifts (x Q : ℕ) :
    allCharacterMean x Q =
      ∑ q ∈ Finset.Icc 1 Q, (Nat.totient q : ℝ)⁻¹ *
        primitiveLiftAdjustedNormSum x q := by
  rw [allCharacterMean]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos := (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨by omega⟩
  rw [sum_norm_adjustedTwistedPsi_eq_primitiveLiftAdjustedNormSum]

theorem sum_maxProgressionError_le_allCharacterMean (x Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      allCharacterMean x Q :=
  sum_maxProgressionError_le_character_sum x Q

end Chen.BombieriVinogradov
