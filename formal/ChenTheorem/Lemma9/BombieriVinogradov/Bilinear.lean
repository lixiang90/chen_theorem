import ChenTheorem.Lemma9.BombieriVinogradov.VaughanIdentity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Bilinear character sums

This file supplies the finite Cauchy--Schwarz layer used after Vaughan's
identity.  It is deliberately stated on one dependent finite set containing
all characters at all moduli, which matches the weights in the character
large sieve.
-/

/-- Characters over all positive moduli at most `Q`. -/
noncomputable def characterIndices (Q : ℕ) :
    Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Finset.Icc 1 Q).sigma fun _q => Finset.univ

/-- Characters with modulus in the conductor interval `(D,Q]`. -/
noncomputable def characterIndicesIoc (D Q : ℕ) :
    Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Finset.Ioc D Q).sigma fun _q => Finset.univ

/-- The large-sieve weight, with nonprimitive characters assigned weight
zero. -/
noncomputable def primitiveCharacterWeight
    (i : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  ((i.1 : ℝ) / (Nat.totient i.1 : ℝ)) *
    if i.2.IsPrimitive then 1 else 0

/-- The `φ(q)⁻¹` weight used on a dyadic conductor interval. -/
noncomputable def primitiveDyadicWeight
    (i : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  (Nat.totient i.1 : ℝ)⁻¹ * if i.2.IsPrimitive then 1 else 0

theorem primitiveCharacterWeight_nonneg
    (i : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveCharacterWeight i := by
  unfold primitiveCharacterWeight
  positivity

theorem primitiveDyadicWeight_nonneg
    (i : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveDyadicWeight i := by
  unfold primitiveDyadicWeight
  positivity

/-- Flatten the nested primitive-character mean into the dependent dyadic
index set. -/
theorem sum_characterIndicesIoc_primitiveDyadicWeight_eq
    (D Q : ℕ)
    (F : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * F i) =
      ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then F ⟨q, χ⟩ else 0 := by
  rw [characterIndicesIoc, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [primitiveDyadicWeight, hp]
  · simp [primitiveDyadicWeight, hp]

/-- The total `1 / φ(q)` mass of primitive characters on `(D,Q]` is at
most the number of moduli, hence at most `Q`. -/
theorem sum_primitiveDyadicWeight_le
    (D Q : ℕ) (hD : 1 ≤ D) :
    (∑ i ∈ characterIndicesIoc D Q, primitiveDyadicWeight i) ≤ Q := by
  rw [characterIndicesIoc, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Ioc D Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveDyadicWeight ⟨q, χ⟩) ≤
        ∑ _q ∈ Finset.Ioc D Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      letI : NeZero q := ⟨hqpos.ne'⟩
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      calc
        (∑ χ : DirichletCharacter ℂ q,
            primitiveDyadicWeight ⟨q, χ⟩) ≤
            ∑ _χ : DirichletCharacter ℂ q, (q.totient : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro χ hχ
          by_cases hp : χ.IsPrimitive
          · simp [primitiveDyadicWeight, hp]
          · simp [primitiveDyadicWeight, hp]
        _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) := by simp
    _ ≤ Q := by
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)

/-- Weighted Cauchy--Schwarz over all primitive characters and moduli. -/
theorem primitiveCharacter_weighted_cauchy_sq
    (Q : ℕ)
    (F G : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i * F i * G i) ^ 2 ≤
      (∑ i ∈ characterIndices Q,
          primitiveCharacterWeight i * F i ^ 2) *
        ∑ i ∈ characterIndices Q,
          primitiveCharacterWeight i * G i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

/-- Weighted Cauchy--Schwarz with the dyadic `φ(q)⁻¹` weight. -/
theorem primitiveCharacter_dyadic_cauchy_sq
    (D Q : ℕ)
    (F G : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * F i * G i) ^ 2 ≤
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * F i ^ 2) *
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * G i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

/-- A character polynomial on an interval `(M, M+N]`. -/
noncomputable def characterIntervalSum {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc M (M + N), a n * χ n

/-- A rectangular bilinear character sum. -/
noncomputable def bilinearCharacterRectangle {q : ℕ}
    (M N K L : ℕ) (a b : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ Finset.Ioc M (M + N),
    ∑ n ∈ Finset.Ioc K (K + L),
      a m * b n * χ (m * n)

/-- A rectangular bilinear sum factors into the product of its two character
polynomials. -/
theorem bilinearCharacterRectangle_eq_mul {q : ℕ}
    (M N K L : ℕ) (a b : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    bilinearCharacterRectangle M N K L a b χ =
      characterIntervalSum M N a χ * characterIntervalSum K L b χ := by
  classical
  rw [bilinearCharacterRectangle, characterIntervalSum,
    characterIntervalSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  ring

/-- The existing character large sieve, rewritten on `characterIndices`. -/
theorem characterIntervalSecondMoment_le
    (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i *
          ‖characterIntervalSum M N a i.2‖ ^ 2) ≤
      ((Q : ℝ) ^ 2 + Real.pi * N) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rw [characterIndices, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveCharacterWeight ⟨q, χ⟩ *
            ‖characterIntervalSum M N a χ‖ ^ 2) =
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp [primitiveCharacterWeight, characterIntervalSum, hp]
      · simp [primitiveCharacterWeight, characterIntervalSum, hp]
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * N) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
      Chen.LargeSieve.large_sieve_character Q M N a

/-- The existing dyadic character large sieve, rewritten on the dependent
character index set used by the bilinear argument. -/
theorem characterIntervalSecondMoment_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖ ^ 2) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Chen.LargeSieve.large_sieve_character_dyadic with
    ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N a hD hDQ
  rw [characterIndicesIoc, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Ioc D Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveDyadicWeight ⟨q, χ⟩ *
            ‖characterIntervalSum M N a χ‖ ^ 2) =
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp [primitiveDyadicWeight, characterIntervalSum, hp]
      · simp [primitiveDyadicWeight, characterIntervalSum, hp]
    _ ≤ C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
      hlarge D Q M N a hD hDQ

/-- Unsquared first-moment consequence of the dyadic character large sieve. -/
theorem characterIntervalMean_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖) ≤
          Real.sqrt
            ((Q : ℝ) *
              (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)) := by
  rcases characterIntervalSecondMoment_dyadic_le with
    ⟨C, hC, hsecond⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N a hD hDQ
  let S : ℝ := ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖characterIntervalSum M N a i.2‖
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun _i => (1 : ℝ))
    (fun i => ‖characterIntervalSum M N a i.2‖)
  have hsq : S ^ 2 ≤
      (Q : ℝ) *
        (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
    dsimp only [S]
    calc
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖characterIntervalSum M N a i.2‖) ^ 2 =
          (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i * 1 *
              ‖characterIntervalSum M N a i.2‖) ^ 2 := by simp
      _ ≤ (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i * 1 ^ 2) *
            ∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N a i.2‖ ^ 2 := hcauchy
      _ ≤ (Q : ℝ) *
            (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
        apply mul_le_mul
        · simpa using sum_primitiveDyadicWeight_le D Q hD
        · exact hsecond D Q M N a hD hDQ
        · exact Finset.sum_nonneg fun i _ =>
            mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
        · positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)
  have hR : 0 ≤
      (Q : ℝ) *
        (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
    positivity
  apply (sq_le_sq₀ hS (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt hR]
  exact hsq

/-- Mean-value bound for rectangular bilinear sums.  Squaring avoids any
loss or side condition from square roots; later dyadic estimates can take
the square root only after inserting concrete nonnegative bounds. -/
theorem bilinearCharacterMean_sq_le
    (Q M N K L : ℕ) (a b : ℕ → ℂ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i *
          ‖characterIntervalSum M N a i.2‖ *
          ‖characterIntervalSum K L b i.2‖) ^ 2 ≤
      (((Q : ℝ) ^ 2 + Real.pi * N) *
          ∑ m ∈ Finset.Ioc M (M + N), ‖a m‖ ^ 2) *
        (((Q : ℝ) ^ 2 + Real.pi * L) *
          ∑ n ∈ Finset.Ioc K (K + L), ‖b n‖ ^ 2) := by
  have hcauchy := primitiveCharacter_weighted_cauchy_sq Q
    (fun i => ‖characterIntervalSum M N a i.2‖)
    (fun i => ‖characterIntervalSum K L b i.2‖)
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact characterIntervalSecondMoment_le Q M N a
  · exact characterIntervalSecondMoment_le Q K L b
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun n _ => sq_nonneg _)

/-- Dyadic-conductor mean-value bound for rectangular bilinear character
sums. -/
theorem bilinearCharacterMean_dyadic_sq_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N K L : ℕ) (a b : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖ *
              ‖characterIntervalSum K L b i.2‖) ^ 2 ≤
          (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              ∑ m ∈ Finset.Ioc M (M + N), ‖a m‖ ^ 2) *
            (C * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc K (K + L), ‖b n‖ ^ 2) := by
  rcases characterIntervalSecondMoment_dyadic_le with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N K L a b hD hDQ
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun i => ‖characterIntervalSum M N a i.2‖)
    (fun i => ‖characterIntervalSum K L b i.2‖)
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact hlarge D Q M N a hD hDQ
  · exact hlarge D Q K L b hD hDQ
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)

end Chen.BombieriVinogradov
