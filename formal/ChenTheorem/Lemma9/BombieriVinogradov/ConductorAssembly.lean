import ChenTheorem.Lemma9.BombieriVinogradov.TypeIIAssembly
import ChenTheorem.Lemma9.BombieriVinogradov.Imprimitive

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Dyadic conductor assembly

The large-sieve estimates are strongest on a conductor block `(D,2D]`.
This file covers all nontrivial primitive conductors by such blocks before
the final choice of Vaughan cutoffs and logarithmic parameters.
-/

/-- The occupied doubling scales between a positive lower cutoff `H` and
the global conductor cutoff `Q`. -/
def conductorDyadicIndices (H Q : ℕ) : Finset ℕ :=
  (typeIIDyadicIndices Q).filter (fun i => 2 ^ i * H < Q)

theorem conductorDyadicIndices_subset (H Q : ℕ) :
    conductorDyadicIndices H Q ⊆ typeIIDyadicIndices Q :=
  Finset.filter_subset _ _

theorem card_conductorDyadicIndices_le (H Q : ℕ) :
    (conductorDyadicIndices H Q).card ≤ Nat.log 2 Q + 1 := by
  exact (Finset.card_le_card (conductorDyadicIndices_subset H Q)).trans_eq
    (by simp [typeIIDyadicIndices])

theorem mem_conductorDyadicIndices_lower_lt
    {H Q i : ℕ} (hi : i ∈ conductorDyadicIndices H Q) :
    2 ^ i * H < Q := by
  exact (Finset.mem_filter.mp hi).2

theorem conductorDyadicBlocks_pairwiseDisjoint (H Q : ℕ) :
    Set.PairwiseDisjoint (conductorDyadicIndices H Q)
      (typeIIDyadicBlock H) := by
  intro i hi j hj hij
  exact typeIIDyadicBlocks_pairwiseDisjoint Q H
    (conductorDyadicIndices_subset H Q hi)
    (conductorDyadicIndices_subset H Q hj) hij

/-- The occupied blocks still cover the whole interval `(H,Q]`. -/
theorem Ioc_subset_conductorDyadicBlocks
    {H Q : ℕ} (hH : 1 ≤ H) :
    Finset.Ioc H Q ⊆
      (conductorDyadicIndices H Q).biUnion (typeIIDyadicBlock H) := by
  intro n hn
  have hncover := Ioc_subset_typeIIDyadicBlocks
    (x := Q) (H := H) hH hn
  rw [Finset.mem_biUnion] at hncover ⊢
  obtain ⟨i, hi, hni⟩ := hncover
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hni⟩
  have hnlo := (Finset.mem_Ioc.mp hn).2
  have hblocklo := (Finset.mem_Ioc.mp hni).1
  omega

/-- The explicit majorant furnished by the three Vaughan pieces on one
dyadic conductor interval. -/
noncomputable def primitiveVaughanMajorant
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ)
    (x U V D Q : ℕ) : ℝ :=
  6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
      Real.log (2 * Q) * Real.log x +
    (Q : ℝ) *
      ((V : ℝ) * Real.log x +
        3 * (C₂ * ((U * V : ℕ) : ℝ) *
              Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
          Real.sqrt Q * Real.log (2 * Q)) +
    ((typeIIInteriorPairs x U V).card : ℝ) *
      Real.sqrt
        (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
          typeIIBoundaryConductorScale D Q U V x *
          Real.log (2 * (x : ℝ)) ^ 5) +
    ((typeIIBoundaryPairs x U V).card : ℝ) *
      ((1 / (2 * Real.pi)) *
        Real.sqrt
          (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
            typeIIBoundaryConductorScale D Q U V x *
            Real.log (2 * (x : ℝ)) ^ 5) *
        (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
          2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
            (x : ℝ)))

/-- The one-block Vaughan estimate in named-majorant form. -/
theorem primitiveAdjustedMean_le_primitiveVaughanMajorant :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x D Q ≤
            primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
              x U V D Q := by
  rcases primitiveAdjustedMean_le_explicit_vaughan_majorants with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hbound⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V D Q hx hU hV hD hDQ hUV hUVx
  simpa only [primitiveVaughanMajorant] using
    hbound x U V D Q hx hU hV hD hDQ hUV hUVx

/-- All primitive conductors in `(H,Q]` are dominated by the sum over the
extended disjoint blocks `(2^i H,2^(i+1)H]`.  Extending the final block
beyond `Q` is harmless because every summand is nonnegative. -/
theorem primitiveAdjustedMean_le_sum_dyadicConductors_from
    (x H Q : ℕ) (hH : 1 ≤ H) :
    primitiveAdjustedMean x H Q ≤
      ∑ i ∈ conductorDyadicIndices H Q,
        primitiveAdjustedMean x (2 ^ i * H) (2 ^ (i + 1) * H) := by
  let F : ℕ → ℝ := fun q =>
    (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0
  let S : Finset ℕ :=
    (conductorDyadicIndices H Q).biUnion (typeIIDyadicBlock H)
  have hsubset : Finset.Ioc H Q ⊆ S := by
    simpa only [S] using
      (Ioc_subset_conductorDyadicBlocks (Q := Q) hH)
  have hF (q : ℕ) : 0 ≤ F q := by
    dsimp only [F]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity)
  rw [primitiveAdjustedMean]
  change (∑ q ∈ Finset.Ioc H Q, F q) ≤ _
  calc
    (∑ q ∈ Finset.Ioc H Q, F q) ≤ ∑ q ∈ S, F q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun q _hqS _hq => hF q)
    _ = ∑ i ∈ conductorDyadicIndices H Q,
          ∑ q ∈ typeIIDyadicBlock H i, F q :=
      Finset.sum_biUnion (conductorDyadicBlocks_pairwiseDisjoint H Q)
    _ = ∑ i ∈ conductorDyadicIndices H Q,
          primitiveAdjustedMean x (2 ^ i * H) (2 ^ (i + 1) * H) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [primitiveAdjustedMean]
      simp only [typeIIDyadicBlock]
      rfl

/-- Specialization of the preceding cover to all nontrivial conductors. -/
theorem primitiveAdjustedMean_le_sum_dyadicConductors (x Q : ℕ) :
    primitiveAdjustedMean x 1 Q ≤
      ∑ i ∈ conductorDyadicIndices 1 Q,
        primitiveAdjustedMean x (2 ^ i) (2 ^ (i + 1)) := by
  simpa only [mul_one] using
    primitiveAdjustedMean_le_sum_dyadicConductors_from x 1 Q (by omega)

/-- Exact split of the primitive mean at a small-conductor threshold. -/
theorem primitiveAdjustedMean_eq_small_add_large
    (x H Q : ℕ) (hHQ : H ≤ Q) :
    primitiveAdjustedMean x 0 Q =
      primitiveAdjustedMean x 0 H + primitiveAdjustedMean x H Q := by
  let F : ℕ → ℝ := fun q =>
    (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0
  rw [primitiveAdjustedMean, primitiveAdjustedMean, primitiveAdjustedMean]
  change (∑ q ∈ Finset.Ioc 0 Q, F q) =
    (∑ q ∈ Finset.Ioc 0 H, F q) + ∑ q ∈ Finset.Ioc H Q, F q
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le H) hHQ]

/-- Exact normal form of the Type-II scale when the upper conductor endpoint
is twice the lower endpoint. -/
theorem typeIIBoundaryConductorScale_double_eq
    (x U V D : ℕ) (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hD : 1 ≤ D) :
    typeIIBoundaryConductorScale D (2 * D) U V x =
      16 * (D : ℝ) ^ 2 / (x : ℝ) +
        2 / (U : ℝ) + 2 / (V : ℝ) + 1 / (D : ℝ) ^ 2 := by
  unfold typeIIBoundaryConductorScale
  push_cast
  field_simp [show (x : ℝ) ≠ 0 by exact_mod_cast (show x ≠ 0 by omega),
    show (U : ℝ) ≠ 0 by exact_mod_cast (show U ≠ 0 by omega),
    show (V : ℝ) ≠ 0 by exact_mod_cast (show V ≠ 0 by omega),
    show (D : ℝ) ≠ 0 by exact_mod_cast (show D ≠ 0 by omega)]
  ring

/-- On the `i`-th conductor block the common Type-II scale has the standard
four-term normal form.  In particular, the mixed large-sieve terms no
longer contain the global conductor cutoff. -/
theorem typeIIBoundaryConductorScale_dyadic_eq
    (x U V i : ℕ) (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    typeIIBoundaryConductorScale (2 ^ i) (2 ^ (i + 1)) U V x =
      16 * ((2 ^ i : ℕ) : ℝ) ^ 2 / (x : ℝ) +
        2 / (U : ℝ) + 2 / (V : ℝ) +
          1 / ((2 ^ i : ℕ) : ℝ) ^ 2 := by
  unfold typeIIBoundaryConductorScale
  rw [pow_succ]
  push_cast
  field_simp [show (x : ℝ) ≠ 0 by exact_mod_cast (show x ≠ 0 by omega),
    show (U : ℝ) ≠ 0 by exact_mod_cast (show U ≠ 0 by omega),
    show (V : ℝ) ≠ 0 by exact_mod_cast (show V ≠ 0 by omega),
    show ((2 : ℝ) ^ i) ≠ 0 by positivity]
  ring

/-- A block-independent envelope for the Type-II scale above conductor `H`
and below conductor `Q`. -/
noncomputable def typeIIConductorScaleEnvelope
    (H Q U V x : ℕ) : ℝ :=
  16 * (Q : ℝ) ^ 2 / (x : ℝ) +
    2 / (U : ℝ) + 2 / (V : ℝ) + 1 / (H : ℝ) ^ 2

theorem typeIIBoundaryConductorScale_dyadic_from_le_envelope
    (x U V H Q i : ℕ)
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : 1 ≤ H)
    (hi : i ∈ conductorDyadicIndices H Q) :
    typeIIBoundaryConductorScale
        (2 ^ i * H) (2 ^ (i + 1) * H) U V x ≤
      typeIIConductorScaleEnvelope H Q U V x := by
  have hpow : 1 ≤ (2 : ℕ) ^ i := one_le_pow₀ (by norm_num)
  have hD : 1 ≤ 2 ^ i * H := Nat.mul_pos (by omega) (by omega)
  have hDQ : 2 ^ i * H ≤ Q :=
    (mem_conductorDyadicIndices_lower_lt hi).le
  have hHD : H ≤ 2 ^ i * H := by
    simpa only [one_mul] using Nat.mul_le_mul_right H hpow
  have hdouble : 2 ^ (i + 1) * H = 2 * (2 ^ i * H) := by
    rw [pow_succ]
    ring
  rw [hdouble,
    typeIIBoundaryConductorScale_double_eq x U V (2 ^ i * H)
      hx hU hV hD]
  unfold typeIIConductorScaleEnvelope
  have hDQR : ((2 ^ i * H : ℕ) : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hDQ
  have hHDR : (H : ℝ) ≤ ((2 ^ i * H : ℕ) : ℝ) := by
    exact_mod_cast hHD
  have hfirst :
      16 * ((2 ^ i * H : ℕ) : ℝ) ^ 2 / (x : ℝ) ≤
        16 * (Q : ℝ) ^ 2 / (x : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    gcongr
  have hlast :
      1 / ((2 ^ i * H : ℕ) : ℝ) ^ 2 ≤ 1 / (H : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  linarith

/-- A block-independent Vaughan majorant for all occupied conductor blocks
above `H` and below `Q`. -/
noncomputable def uniformPrimitiveVaughanMajorant
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ)
    (x U V H Q : ℕ) : ℝ :=
  6 * ((2 * Q : ℕ) : ℝ) * (min U x : ℝ) * Real.sqrt (2 * Q) *
      Real.log (2 * ((2 * Q : ℕ) : ℝ)) * Real.log x +
    ((2 * Q : ℕ) : ℝ) *
      ((V : ℝ) * Real.log x +
        3 * (C₂ * ((U * V : ℕ) : ℝ) *
              Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
          Real.sqrt (2 * Q) * Real.log (2 * ((2 * Q : ℕ) : ℝ))) +
    ((typeIIInteriorPairs x U V).card : ℝ) *
      Real.sqrt
        (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
          typeIIConductorScaleEnvelope H Q U V x *
          Real.log (2 * (x : ℝ)) ^ 5) +
    ((typeIIBoundaryPairs x U V).card : ℝ) *
      ((1 / (2 * Real.pi)) *
        Real.sqrt
          (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
            typeIIConductorScaleEnvelope H Q U V x *
            Real.log (2 * (x : ℝ)) ^ 5) *
        (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
          2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
            (x : ℝ)))

theorem uniformPrimitiveVaughanMajorant_nonneg
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ)
    (x U V H Q : ℕ)
    (hC₂ : 0 ≤ C₂) (_hCᵢ₁ : 0 ≤ Cᵢ₁) (_hCᵦ₁ : 0 ≤ Cᵦ₁)
    (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hH : 1 ≤ H) (hQ : 1 ≤ Q) :
    0 ≤ uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
      x U V H Q := by
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hlog2x : 0 ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * x by omega))
  have hlogUV : 0 ≤ Real.log ((U * V : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ U * V by
        exact Nat.mul_pos (by omega) (by omega)))
  have hlogQ : 0 ≤ Real.log (2 * ((2 * Q : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (2 * Q) by omega))
  have hscale : 0 ≤ typeIIConductorScaleEnvelope H Q U V x := by
    unfold typeIIConductorScaleEnvelope
    positivity
  have hmass :
      0 ≤ 4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (x : ℝ) := by
    have hlog : 0 ≤ Real.log (1 + (x : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 1 + x by omega))
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num)
        (by unfold perronUpperPoint; positivity)) hlog
    · exact div_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)
  unfold uniformPrimitiveVaughanMajorant
  positivity

theorem primitiveVaughanMajorant_dyadic_le_uniform
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ)
    (x U V H Q i : ℕ)
    (hC₂ : 0 ≤ C₂) (hCᵢ₁ : 0 ≤ Cᵢ₁) (hCᵦ₁ : 0 ≤ Cᵦ₁)
    (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : 1 ≤ H)
    (hi : i ∈ conductorDyadicIndices H Q) :
    primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
        x U V (2 ^ i * H) (2 ^ (i + 1) * H) ≤
      uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
        x U V H Q := by
  have hDltQ := mem_conductorDyadicIndices_lower_lt hi
  have hdouble : 2 ^ (i + 1) * H = 2 * (2 ^ i * H) := by
    rw [pow_succ]
    ring
  have hblockQ : 2 ^ (i + 1) * H ≤ 2 * Q := by
    rw [hdouble]
    omega
  have hblockQR : ((2 ^ (i + 1) * H : ℕ) : ℝ) ≤ (2 * Q : ℕ) := by
    exact_mod_cast hblockQ
  have hblockQR' :
      ((2 ^ (i + 1) * H : ℕ) : ℝ) ≤ 2 * (Q : ℝ) := by
    exact_mod_cast hblockQ
  have hlogBlock :
      Real.log (2 * ((2 ^ (i + 1) * H : ℕ) : ℝ)) ≤
        Real.log (2 * ((2 * Q : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · gcongr
  have hscale := typeIIBoundaryConductorScale_dyadic_from_le_envelope
    x U V H Q i (by omega) hU hV hH hi
  unfold primitiveVaughanMajorant uniformPrimitiveVaughanMajorant
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hlogUV : 0 ≤ Real.log ((U * V : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ U * V by
        exact Nat.mul_pos (by omega) (by omega)))
  have hlogBlock0 :
      0 ≤ Real.log (2 * ((2 ^ (i + 1) * H : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 ^ (i + 1) * H) by
        have hp : 0 < (2 : ℕ) ^ (i + 1) := pow_pos (by norm_num) _
        exact Nat.mul_pos (by omega) (Nat.mul_pos hp (by omega))))
  have hlogGlobal0 :
      0 ≤ Real.log (2 * ((2 * Q : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 * Q) by
        have hp : 0 < (2 : ℕ) ^ i := pow_pos (by norm_num) _
        have hQ : 0 < Q := (Nat.mul_pos hp (by omega)).trans hDltQ
        omega))
  have hlog2x : 0 ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * x by omega))
  have hlog2xpow : 0 ≤ Real.log (2 * (x : ℝ)) ^ 5 :=
    pow_nonneg hlog2x _
  have hmass :
      0 ≤ 4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (x : ℝ) := by
    have hlog : 0 ≤ Real.log (1 + (x : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 1 + x by omega))
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num)
        (by unfold perronUpperPoint; positivity)) hlog
    · exact div_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)
  gcongr

/-- Dyadic assembly beginning above a positive small-conductor cutoff `H`.
This is the form paired with a separate Siegel--Walfisz estimate on
conductors at most `H`. -/
theorem primitiveAdjustedMean_le_sum_dyadicVaughanMajorants_from :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V H Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ H →
          2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x H Q ≤
            ∑ i ∈ conductorDyadicIndices H Q,
              primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
                x U V (2 ^ i * H) (2 ^ (i + 1) * H) := by
  rcases primitiveAdjustedMean_le_primitiveVaughanMajorant with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hblock⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V H Q hx hU hV hH hUV hUVx
  calc
    primitiveAdjustedMean x H Q ≤
        ∑ i ∈ conductorDyadicIndices H Q,
          primitiveAdjustedMean x (2 ^ i * H) (2 ^ (i + 1) * H) :=
      primitiveAdjustedMean_le_sum_dyadicConductors_from x H Q hH
    _ ≤ ∑ i ∈ conductorDyadicIndices H Q,
          primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V (2 ^ i * H) (2 ^ (i + 1) * H) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpow : 0 < (2 : ℕ) ^ i := pow_pos (by norm_num) i
      have hDi : 1 ≤ 2 ^ i * H := Nat.mul_pos hpow (by omega)
      have hdouble : 2 ^ (i + 1) * H = 2 * (2 ^ i * H) := by
        rw [pow_succ]
        ring
      exact hblock x U V (2 ^ i * H) (2 ^ (i + 1) * H)
        hx hU hV hDi (by rw [hdouble]; omega) hUV hUVx

/-- Final conductor-block assembly: the whole non-small primitive mean is
bounded by the number of occupied blocks times one uniform Vaughan
majorant. -/
theorem primitiveAdjustedMean_le_card_mul_uniformVaughanMajorant :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V H Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ H →
          2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x H Q ≤
            ((conductorDyadicIndices H Q).card : ℝ) *
              uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
                x U V H Q := by
  rcases primitiveAdjustedMean_le_sum_dyadicVaughanMajorants_from with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hdyadic⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V H Q hx hU hV hH hUV hUVx
  calc
    primitiveAdjustedMean x H Q ≤
        ∑ i ∈ conductorDyadicIndices H Q,
          primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V (2 ^ i * H) (2 ^ (i + 1) * H) :=
      hdyadic x U V H Q hx hU hV hH hUV hUVx
    _ ≤ ∑ _i ∈ conductorDyadicIndices H Q,
          uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V H Q := by
      apply Finset.sum_le_sum
      intro i hi
      exact primitiveVaughanMajorant_dyadic_le_uniform
        C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x U V H Q i
        hC₂.le hCᵢ₁.le hCᵦ₁.le hx hU hV hH hi
    _ = ((conductorDyadicIndices H Q).card : ℝ) *
          uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V H Q := by simp

/-- The same assembly with the occupied-block count replaced by its simple
`log₂ Q + 1` upper bound. -/
theorem primitiveAdjustedMean_le_log_mul_uniformVaughanMajorant :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V H Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ H → 1 ≤ Q →
          2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x H Q ≤
            ((Nat.log 2 Q + 1 : ℕ) : ℝ) *
              uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
                x U V H Q := by
  rcases primitiveAdjustedMean_le_card_mul_uniformVaughanMajorant with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hbound⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V H Q hx hU hV hH hQ hUV hUVx
  calc
    primitiveAdjustedMean x H Q ≤
        ((conductorDyadicIndices H Q).card : ℝ) *
          uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V H Q :=
      hbound x U V H Q hx hU hV hH hUV hUVx
    _ ≤ ((Nat.log 2 Q + 1 : ℕ) : ℝ) *
          uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V H Q := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_conductorDyadicIndices_le H Q
      · exact uniformPrimitiveVaughanMajorant_nonneg
          C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x U V H Q
          hC₂.le hCᵢ₁.le hCᵦ₁.le hx hU hV hH hQ

/-- Progression errors split into the small primitive-conductor mean, the
large-conductor mean, and the already controlled imprimitive lifting error. -/
theorem sum_maxProgressionError_le_small_add_large_add_error
    (x H Q : ℕ) (hx : 2 ≤ x) (hHQ : H ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      (harmonic Q : ℝ) ^ 2 *
          (primitiveAdjustedMean x 0 H + primitiveAdjustedMean x H Q) +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x := by
  simpa only [primitiveAdjustedMean_eq_small_add_large x H Q hHQ] using
    sum_maxProgressionError_le_harmonic_sq_mul_primitiveAdjustedMean_add_error
      x Q hx

/-- Fully explicit reduction of the original progression-error mean.  The
only unsimplified arithmetic term is the small-conductor primitive mean;
the complementary range is bounded by the proved Vaughan majorant. -/
theorem sum_maxProgressionError_le_small_add_uniformVaughan_add_error :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V H Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ H → 1 ≤ Q → H ≤ Q →
          2 ≤ U * V → U * V ≤ x →
          (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
            (harmonic Q : ℝ) ^ 2 *
                (primitiveAdjustedMean x 0 H +
                  ((Nat.log 2 Q + 1 : ℕ) : ℝ) *
                    uniformPrimitiveVaughanMajorant
                      C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x U V H Q) +
              2 * (Q : ℝ) * (Q + 1 : ℝ) *
                (Nat.log 2 x + 1 : ℝ) * Real.log x := by
  rcases primitiveAdjustedMean_le_log_mul_uniformVaughanMajorant with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hlarge⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V H Q hx hU hV hH hQ hHQ hUV hUVx
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
        (harmonic Q : ℝ) ^ 2 *
            (primitiveAdjustedMean x 0 H + primitiveAdjustedMean x H Q) +
          2 * (Q : ℝ) * (Q + 1 : ℝ) *
            (Nat.log 2 x + 1 : ℝ) * Real.log x :=
      sum_maxProgressionError_le_small_add_large_add_error x H Q hx hHQ
    _ ≤ (harmonic Q : ℝ) ^ 2 *
            (primitiveAdjustedMean x 0 H +
              ((Nat.log 2 Q + 1 : ℕ) : ℝ) *
                uniformPrimitiveVaughanMajorant
                  C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x U V H Q) +
          2 * (Q : ℝ) * (Q + 1 : ℝ) *
            (Nat.log 2 x + 1 : ℝ) * Real.log x := by
      gcongr
      exact hlarge x U V H Q hx hU hV hH hQ hUV hUVx

/-- Dyadic conductor assembly of the complete primitive Vaughan estimate. -/
theorem primitiveAdjustedMean_le_sum_dyadicVaughanMajorants :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x 1 Q ≤
            ∑ i ∈ conductorDyadicIndices 1 Q,
              primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
                x U V (2 ^ i) (2 ^ (i + 1)) := by
  rcases primitiveAdjustedMean_le_primitiveVaughanMajorant with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hblock⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V Q hx hU hV hUV hUVx
  calc
    primitiveAdjustedMean x 1 Q ≤
        ∑ i ∈ conductorDyadicIndices 1 Q,
          primitiveAdjustedMean x (2 ^ i) (2 ^ (i + 1)) :=
      primitiveAdjustedMean_le_sum_dyadicConductors x Q
    _ ≤ ∑ i ∈ conductorDyadicIndices 1 Q,
          primitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
            x U V (2 ^ i) (2 ^ (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hblock x U V (2 ^ i) (2 ^ (i + 1))
        hx hU hV (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))
        (by rw [pow_succ]; omega) hUV hUVx

end Chen.BombieriVinogradov
