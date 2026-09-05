import ChenTheorem.Lemma9.BombieriVinogradov.TypeI

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Primitive-character mean value

This file performs the exact triangle-inequality reduction from the adjusted
von-Mangoldt sums to the three pieces of Vaughan's identity.  The remaining
analytic task is to estimate the two Type-I means and the Type-II mean on
dyadic rectangles.
-/

theorem adjustedTwistedPsi_eq_vaughanTypeSums_of_primitive
    {q : ℕ} (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (x U V : ℕ) :
    adjustedTwistedPsi x χ =
      vaughanTypeIOneSum x U χ + vaughanTypeITwoSum x U V χ +
        vaughanTypeIISum x U V χ := by
  letI : NeZero q := ⟨by omega⟩
  have hχne : χ ≠ 1 := by
    intro hχone
    subst χ
    have hone : (1 : ℕ) = q := by
      calc
        1 = (1 : DirichletCharacter ℂ q).conductor := by
          symm
          exact DirichletCharacter.conductor_one
        _ = q := hχ
    omega
  rw [adjustedTwistedPsi, if_neg hχne, sub_zero,
    twistedPsi_eq_vaughanTypes x U V χ]

theorem norm_adjustedTwistedPsi_le_vaughanTypeSums
    {q : ℕ} (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (x U V : ℕ) :
    ‖adjustedTwistedPsi x χ‖ ≤
      ‖vaughanTypeIOneSum x U χ‖ + ‖vaughanTypeITwoSum x U V χ‖ +
        ‖vaughanTypeIISum x U V χ‖ := by
  rw [adjustedTwistedPsi_eq_vaughanTypeSums_of_primitive
    hq χ hχ x U V]
  exact norm_add_le_of_le (norm_add_le _ _) (le_refl _)

/-- Primitive-character mean on a conductor interval `(D,Q]`. -/
noncomputable def primitiveAdjustedMean (x D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0

noncomputable def primitiveTypeIOneMean (x U D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0

noncomputable def primitiveTypeITwoMean (x U V D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0

noncomputable def primitiveTypeIIMean (x U V D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0

theorem primitiveAdjustedMean_eq_characterIndicesIoc
    (x D Q : ℕ) :
    primitiveAdjustedMean x D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖adjustedTwistedPsi x i.2‖ := by
  rw [primitiveAdjustedMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeIOneMean_eq_characterIndicesIoc
    (x U D Q : ℕ) :
    primitiveTypeIOneMean x U D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeIOneSum x U i.2‖ := by
  rw [primitiveTypeIOneMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeITwoMean_eq_characterIndicesIoc
    (x U V D Q : ℕ) :
    primitiveTypeITwoMean x U V D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeITwoSum x U V i.2‖ := by
  rw [primitiveTypeITwoMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeIIMean_eq_characterIndicesIoc
    (x U V D Q : ℕ) :
    primitiveTypeIIMean x U V D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeIISum x U V i.2‖ := by
  rw [primitiveTypeIIMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveAdjustedMean_nonneg (x D Q : ℕ) :
    0 ≤ primitiveAdjustedMean x D Q := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity)

/-- Exact reduction of the primitive mean to Vaughan's three pieces. -/
theorem primitiveAdjustedMean_le_vaughanTypeMeans
    (x U V D Q : ℕ) (hD : 1 ≤ D) :
    primitiveAdjustedMean x D Q ≤
      primitiveTypeIOneMean x U D Q +
        primitiveTypeITwoMean x U V D Q +
          primitiveTypeIIMean x U V D Q := by
  rw [primitiveAdjustedMean, primitiveTypeIOneMean,
    primitiveTypeITwoMean, primitiveTypeIIMean]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have hqD := (Finset.mem_Ioc.mp hq).1
  have hq1 : 1 < q := lt_of_le_of_lt hD hqD
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro χ hχmem
    by_cases hχ : χ.IsPrimitive
    · simp only [hχ, if_true]
      exact norm_adjustedTwistedPsi_le_vaughanTypeSums
        hq1 χ hχ x U V
    · simp [hχ]
  calc
    (Nat.totient q : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
      (Nat.totient q : ℝ)⁻¹ *
        ((∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0) := by
      ring

/-- The first Vaughan Type-I piece is short enough to be summed over the
whole conductor interval using the pointwise Pólya--Vinogradov bound.  The
factor `1/φ(q)` cancels the number of characters modulo `q`; bounding every
remaining occurrence of `q` by `Q` gives the displayed uniform estimate. -/
theorem primitiveTypeIOneMean_le
    (x U D Q : ℕ) (hx : 2 ≤ x) (hD : 1 ≤ D) (hDQ : D ≤ Q) :
    primitiveTypeIOneMean x U D Q ≤
      6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
        Real.log (2 * Q) * Real.log x := by
  let A : ℝ :=
    6 * (min U x : ℝ) * Real.sqrt Q *
      Real.log (2 * Q) * Real.log x
  have hlogQ : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * Q by omega))
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  rw [primitiveTypeIOneMean]
  calc
    (∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
        ∑ _q ∈ Finset.Ioc D Q, A := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqdata := Finset.mem_Ioc.mp hqmem
      have hq2 : 2 ≤ q := by omega
      have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
      letI : NeZero q := ⟨by omega⟩
      have hpoint :
          ∀ χ : DirichletCharacter ℂ q,
            (if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤ A := by
        intro χ
        by_cases hχ : χ.IsPrimitive
        · rw [if_pos hχ]
          have hraw := norm_vaughanTypeIOneSum_le hχ hq2 x U hx
          refine hraw.trans ?_
          dsimp only [A]
          have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) := by
            exact Real.sqrt_le_sqrt (by exact_mod_cast hqdata.2)
          have hlog : Real.log (2 * (q : ℝ)) ≤
              Real.log (2 * (Q : ℝ)) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast Nat.mul_le_mul_left 2 hqdata.2
          gcongr
        · rw [if_neg hχ]
          exact hA
      have hsum :
          (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
            ∑ _χ : DirichletCharacter ℂ q, A := by
        exact Finset.sum_le_sum fun χ _ => hpoint χ
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      calc
        (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
            (q.totient : ℝ)⁻¹ *
              ∑ _χ : DirichletCharacter ℂ q, A :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
        _ = A := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) * A := by simp
    _ ≤ (Q : ℝ) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)
    _ = 6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
          Real.log (2 * Q) * Real.log x := by
      dsimp only [A]
      ring

/-- Conductor-interval mean bound for Vaughan's second Type-I piece.  As in
`primitiveTypeIOneMean_le`, the reciprocal-totient weight cancels the number
of characters, after which the pointwise short-support estimate is made
uniform by replacing `q` with `Q`. -/
theorem primitiveTypeITwoMean_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x U V D Q : ℕ), 2 ≤ x → 1 ≤ D → D ≤ Q →
        2 ≤ U * V → U * V ≤ x →
          primitiveTypeITwoMean x U V D Q ≤
            (Q : ℝ) *
              ((V : ℝ) * Real.log x +
                3 * (C * ((U * V : ℕ) : ℝ) *
                      (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                        ((U * V : ℕ) : ℝ)) *
                  Real.sqrt Q * Real.log (2 * Q)) := by
  rcases norm_vaughanTypeITwoSum_le with ⟨C, hC, hpointwise⟩
  refine ⟨C, hC, ?_⟩
  intro x U V D Q hx hD hDQ hUV2 hUVx
  let B : ℝ :=
    (V : ℝ) * Real.log x +
      3 * (C * ((U * V : ℕ) : ℝ) *
            (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
              ((U * V : ℕ) : ℝ)) *
        Real.sqrt Q * Real.log (2 * Q)
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hlogUV : 0 ≤ Real.log ((U * V : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ U * V by omega))
  have hlogQ : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * Q by omega))
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  rw [primitiveTypeITwoMean]
  calc
    (∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
        ∑ _q ∈ Finset.Ioc D Q, B := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqdata := Finset.mem_Ioc.mp hqmem
      have hq2 : 2 ≤ q := by omega
      letI : NeZero q := ⟨by omega⟩
      have hcharBound :
          ∀ χ : DirichletCharacter ℂ q,
            (if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤ B := by
        intro χ
        by_cases hχ : χ.IsPrimitive
        · rw [if_pos hχ]
          have hraw := hpointwise q inferInstance χ hχ hq2
            x U V hx hUV2 hUVx
          refine hraw.trans ?_
          dsimp only [B]
          have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast hqdata.2)
          have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
            Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
          have hlog : Real.log (2 * (q : ℝ)) ≤
              Real.log (2 * (Q : ℝ)) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast Nat.mul_le_mul_left 2 hqdata.2
          gcongr
        · rw [if_neg hχ]
          exact hB
      have hsum :
          (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
            ∑ _χ : DirichletCharacter ℂ q, B :=
        Finset.sum_le_sum fun χ _ => hcharBound χ
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      calc
        (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
            (q.totient : ℝ)⁻¹ *
              ∑ _χ : DirichletCharacter ℂ q, B :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
        _ = B := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) * B := by simp
    _ ≤ (Q : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)
    _ = (Q : ℝ) *
          ((V : ℝ) * Real.log x +
            3 * (C * ((U * V : ℕ) : ℝ) *
                  (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                    ((U * V : ℕ) : ℝ)) *
              Real.sqrt Q * Real.log (2 * Q)) := by
      rfl

end Chen.BombieriVinogradov
