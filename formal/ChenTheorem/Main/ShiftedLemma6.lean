import ChenTheorem.Main.ShiftedLemma5Arithmetic
import ChenTheorem.Lemma6.Core

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! # Fixed-shift analogue of Lemma 6

This file starts the conductor reduction for the primitive-character error.
The analytic scale remains `x`; only the unit phase is evaluated at `h` and
the outer sieve moduli are coprime to `h`.
-/

noncomputable def shiftedLemma6PrimitiveBlock
    (h x m l : ℕ) : ℂ :=
  primComplexSum l (fun χ =>
    starRingEnd ℂ (χ (h : ZMod l)) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) m),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))

theorem shiftedLemma6PrimitiveBlock_mul_left
    (h x l m : ℕ) (_hl : 0 < l) :
    shiftedLemma6PrimitiveBlock h x (l * m) l =
      shiftedLemma6PrimitiveBlock h x m l := by
  letI : NeZero l := ⟨_hl.ne'⟩
  unfold shiftedLemma6PrimitiveBlock primComplexSum
  apply tsum_congr
  intro χ
  by_cases hχ : χ.IsPrimitive
  · rw [if_pos hχ, if_pos hχ]
    let S := (chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) m)
    let P := fun q : ℕ × ℕ => Nat.Coprime (q.1 * q.2) l
    have hfilter :
        (chenPairs x).filter
            (fun q => Nat.Coprime (q.1 * q.2) (l * m)) =
          S.filter P := by
      ext q
      simp only [S, P, Finset.mem_filter]
      rw [Nat.coprime_mul_iff_right]
      tauto
    rw [hfilter]
    have hzero :
        ∑ q ∈ S.filter (fun q => ¬P q),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                χ (q.1 * q.2 * n : ZMod l) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqnot : ¬Nat.Coprime (q.1 * q.2) l :=
        (Finset.mem_filter.mp hq).2
      apply Finset.sum_eq_zero
      intro n hn
      have hprodnot : ¬Nat.Coprime (q.1 * q.2 * n) l := by
        intro hprod
        exact hqnot (Nat.Coprime.of_dvd_left
          (by exact dvd_mul_right (q.1 * q.2) n) hprod)
      have hnonunit :
          ¬IsUnit ((q.1 * q.2 * n : ℕ) : ZMod l) := by
        intro hu
        exact hprodnot ((ZMod.isUnit_iff_coprime
          (q.1 * q.2 * n) l).1 hu)
      have hnonunit' :
          ¬IsUnit ((q.1 : ZMod l) * q.2 * n) := by
        simpa only [Nat.cast_mul] using hnonunit
      have hχzero : χ (q.1 * q.2 * n : ZMod l) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit'
      rw [hχzero, mul_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := S) (p := P)
      (f := fun q =>
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))
    rw [hzero, add_zero] at hsplit
    simpa only [S] using congrArg
      (fun z : ℂ => starRingEnd ℂ (χ (h : ZMod l)) * z) hsplit
  · rw [if_neg hχ, if_neg hχ]

theorem shiftedLemma6_divisor_cofactor_data
    {h x d l : ℕ} (hd : Squarefree d) (hl : l ∈ d.divisors) :
    lemma6TotientWeight d =
        lemma6TotientWeight l * lemma6TotientWeight (d / l) ∧
      shiftedLemma6PrimitiveBlock h x d l =
        shiftedLemma6PrimitiveBlock h x (d / l) l := by
  have hld : l ∣ d := Nat.dvd_of_mem_divisors hl
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp hl).2
  have hlpos : 0 < l :=
    Nat.pos_of_dvd_of_pos hld (Nat.pos_of_ne_zero hd0)
  have hquotpos : 0 < d / l := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld) hlpos
  have hprod : l * (d / l) = d := Nat.mul_div_cancel' hld
  have hcop : l.Coprime (d / l) :=
    Nat.coprime_of_squarefree_mul (hprod.symm ▸ hd)
  constructor
  · calc
      lemma6TotientWeight d =
          lemma6TotientWeight (l * (d / l)) := congrArg _ hprod.symm
      _ = lemma6TotientWeight l * lemma6TotientWeight (d / l) :=
        lemma6TotientWeight_mul hlpos.ne' hquotpos.ne' hcop
  · calc
      shiftedLemma6PrimitiveBlock h x d l =
          shiftedLemma6PrimitiveBlock h x (l * (d / l)) l :=
        congrArg (fun m => shiftedLemma6PrimitiveBlock h x m l)
          hprod.symm
      _ = shiftedLemma6PrimitiveBlock h x (d / l) l :=
        shiftedLemma6PrimitiveBlock_mul_left h x l (d / l) hlpos

theorem shiftedPrimitiveCharacterContribution_eq_sum_primitive
    {h x d : ℕ} (hd : 0 < d) :
    shiftedPrimitiveCharacterContribution h x d =
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else shiftedLemma6PrimitiveBlock h x d k.1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  unfold shiftedPrimitiveCharacterContribution nontrivialCharSum
  rw [dif_neg hd.ne', sum_characters_eq_sum_primitiveLifts,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2) hd).ne'⟩
  by_cases hkone : k.1 = 1
  · rw [if_pos hkone]
    apply Finset.sum_eq_zero
    intro ψ hψ
    rw [if_pos]
    change DirichletCharacter.changeLevel
        (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1
    rw [DirichletCharacter.changeLevel_eq_one_iff]
    apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    exact ψ.2.trans hkone
  · rw [if_neg hkone]
    unfold shiftedLemma6PrimitiveBlock primComplexSum
    rw [← sum_primitive_subtype_eq_tsum]
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hliftne : primitiveLift d ⟨k, ψ⟩ ≠ 1 := by
      change DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors k.2) ψ.1 ≠ 1
      intro hliftone
      have hψone : ψ.1 = 1 := by
        exact (DirichletCharacter.changeLevel_eq_one_iff
          (R := ℂ) (Nat.dvd_of_mem_divisors k.2)).mp hliftone
      apply hkone
      have hcond : ψ.1.conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp hψone
      exact ψ.2.symm.trans hcond
    rw [if_neg hliftne]
    change
      starRingEnd ℂ ((primitiveLift d ⟨k, ψ⟩).primitiveCharacter h) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                (primitiveLift d ⟨k, ψ⟩).primitiveCharacter
                  (q.1 * q.2 * n) =
        starRingEnd ℂ (ψ.1 h) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                ψ.1 (q.1 * q.2 * n)
    rw [primitiveLift_primitiveCharacter_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro n hn
    have happ := primitiveLift_primitiveCharacter_apply
      d ⟨k, ψ⟩ (q.1 * q.2 * n)
    simpa only [Nat.cast_mul] using congrArg
      (fun z : ℂ => (smoothedMKernel x q n : ℂ) * z) happ

theorem shiftedPrimitiveCharacterContribution_norm_le_sum_primitive
    {h x d : ℕ} (hd : 0 < d) :
    ‖shiftedPrimitiveCharacterContribution h x d‖ ≤
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖ := by
  rw [shiftedPrimitiveCharacterContribution_eq_sum_primitive hd]
  calc
    ‖∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else shiftedLemma6PrimitiveBlock h x d k.1‖ ≤
      ∑ k : ↥d.divisors,
        ‖if k.1 = 1 then 0
          else shiftedLemma6PrimitiveBlock h x d k.1‖ :=
      norm_sum_le _ _
    _ = ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkone : k.1 = 1 <;> simp [hkone]

noncomputable def shiftedLemma6ConductorMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    lemma6TotientWeight d *
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else ‖shiftedLemma6PrimitiveBlock h x d k.1‖

theorem shiftedMTwo_le_shiftedLemma6ConductorMajorant
    (h x : ℕ) (ε : ℝ) :
    shiftedMTwo h x ε ≤ shiftedLemma6ConductorMajorant h x ε := by
  unfold shiftedMTwo shiftedLemma6ConductorMajorant
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by
    have hddata := (Finset.mem_filter.mp hd).2
    omega
  apply mul_le_mul_of_nonneg_left
    (shiftedPrimitiveCharacterContribution_norm_le_sum_primitive hdpos)
  exact lemma6TotientWeight_nonneg d

theorem divisor_mem_shiftedSieveModuli
    {h x l d : ℕ} {ε : ℝ}
    (hd : d ∈ shiftedSieveModuli h x ε)
    (hlpos : 0 < l) (hld : l ∣ d) :
    l ∈ shiftedSieveModuli h x ε := by
  rw [shiftedSieveModuli, Finset.mem_filter] at hd ⊢
  have hldle : l ≤ d := Nat.le_of_dvd (by omega) hld
  refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hldle
      (Finset.mem_range.mp hd.1)), ?_⟩
  refine ⟨hlpos, Nat.Coprime.of_dvd_left hld hd.2.2.1, ?_⟩
  exact (by exact_mod_cast hldle : (l : ℝ) ≤ d).trans hd.2.2.2

noncomputable def shiftedLemma6SplitConductorMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    if _hd : Squarefree d then
      ∑ k ∈ d.divisors,
        if k = 1 then 0
        else lemma6TotientWeight (d / k) * lemma6TotientWeight k *
          ‖shiftedLemma6PrimitiveBlock h x (d / k) k‖
    else 0

noncomputable def shiftedLemma6SplitPairRange
    (h x : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((shiftedSieveModuli h x ε).filter Squarefree).biUnion
    Nat.divisorsAntidiagonal

noncomputable def shiftedLemma6SplitPairTerm
    (h x : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.2 = 1 then 0
  else lemma6TotientWeight p.1 * lemma6TotientWeight p.2 *
    ‖shiftedLemma6PrimitiveBlock h x p.1 p.2‖

theorem shiftedLemma6SplitPairTerm_nonneg
    (h x : ℕ) (p : ℕ × ℕ) :
    0 ≤ shiftedLemma6SplitPairTerm h x p := by
  unfold shiftedLemma6SplitPairTerm
  split_ifs
  · positivity
  · exact mul_nonneg
      (mul_nonneg (lemma6TotientWeight_nonneg p.1)
        (lemma6TotientWeight_nonneg p.2)) (norm_nonneg _)

theorem shiftedLemma6ConductorMajorant_eq_split
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6ConductorMajorant h x ε =
      shiftedLemma6SplitConductorMajorant h x ε := by
  unfold shiftedLemma6ConductorMajorant
    shiftedLemma6SplitConductorMajorant
  apply Finset.sum_congr rfl
  intro d hdmem
  by_cases hdsq : Squarefree d
  · rw [dif_pos hdsq, Finset.mul_sum, ← d.divisors.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkone : k.1 = 1
    · simp [hkone]
    · rw [if_neg hkone, if_neg hkone]
      have hdata := shiftedLemma6_divisor_cofactor_data
        (h := h) (x := x) hdsq k.2
      rw [hdata.1, hdata.2]
      ring
  · rw [dif_neg hdsq]
    have hweight : lemma6TotientWeight d = 0 := by
      unfold lemma6TotientWeight
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
      norm_num
    rw [hweight, zero_mul]

theorem shiftedLemma6SplitConductorMajorant_eq_pairSum
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6SplitConductorMajorant h x ε =
      ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
        shiftedLemma6SplitPairTerm h x p := by
  have hdisj : Set.PairwiseDisjoint
      ((shiftedSieveModuli h x ε).filter Squarefree)
      Nat.divisorsAntidiagonal := by
    intro d₁ hd₁ d₂ hd₂ hdne
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have hprod₁ := (Nat.mem_divisorsAntidiagonal.mp hp₁).1
    have hprod₂ := (Nat.mem_divisorsAntidiagonal.mp hp₂).1
    exact hdne (hprod₁.symm.trans hprod₂)
  calc
    shiftedLemma6SplitConductorMajorant h x ε =
        ∑ d ∈ (shiftedSieveModuli h x ε).filter Squarefree,
          ∑ p ∈ d.divisorsAntidiagonal,
            shiftedLemma6SplitPairTerm h x p := by
      unfold shiftedLemma6SplitConductorMajorant
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdsq : Squarefree d
      · rw [dif_pos hdsq, if_pos hdsq]
        rw [← Nat.sum_divisorsAntidiagonal'
          (f := fun m k =>
            if k = 1 then 0
            else lemma6TotientWeight m * lemma6TotientWeight k *
              ‖shiftedLemma6PrimitiveBlock h x m k‖)]
        unfold shiftedLemma6SplitPairTerm
        rfl
      · rw [dif_neg hdsq, if_neg hdsq]
    _ = ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
          shiftedLemma6SplitPairTerm h x p := by
      unfold shiftedLemma6SplitPairRange
      exact (Finset.sum_biUnion hdisj).symm

theorem shiftedLemma6SplitPairRange_subset
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6SplitPairRange h x ε ⊆
      shiftedSieveModuli h x ε ×ˢ shiftedSieveModuli h x ε := by
  intro p hp
  rw [shiftedLemma6SplitPairRange, Finset.mem_biUnion] at hp
  obtain ⟨d, hd, hp⟩ := hp
  have hdmem : d ∈ shiftedSieveModuli h x ε :=
    (Finset.mem_filter.mp hd).1
  have hp₁pos : 0 < p.1 := Nat.pos_of_ne_zero
    (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
  have hp₂pos : 0 < p.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
  rw [Finset.mem_product]
  exact ⟨divisor_mem_shiftedSieveModuli hdmem hp₁pos
      (Nat.dvd_of_mem_divisors
        (Nat.fst_mem_divisors_of_mem_antidiagonal hp)),
    divisor_mem_shiftedSieveModuli hdmem hp₂pos
      (Nat.dvd_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal hp))⟩

noncomputable def shiftedLemma6IndependentMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ shiftedSieveModuli h x ε ×ˢ shiftedSieveModuli h x ε,
    shiftedLemma6SplitPairTerm h x p

theorem shiftedLemma6IndependentMajorant_eq_bisum
    (h x : ℕ) (ε : ℝ) :
    shiftedLemma6IndependentMajorant h x ε =
      ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ∑ l ∈ shiftedSieveModuli h x ε,
            if l = 1 then 0
            else lemma6TotientWeight l *
              ‖shiftedLemma6PrimitiveBlock h x m l‖ := by
  unfold shiftedLemma6IndependentMajorant
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  unfold shiftedLemma6SplitPairTerm
  by_cases hlone : l = 1
  · simp [hlone]
  · simp only [hlone, ↓reduceIte]
    ring

theorem shiftedMTwo_le_shiftedLemma6IndependentMajorant
    (h x : ℕ) (ε : ℝ) :
    shiftedMTwo h x ε ≤
      shiftedLemma6IndependentMajorant h x ε := by
  calc
    shiftedMTwo h x ε ≤ shiftedLemma6ConductorMajorant h x ε :=
      shiftedMTwo_le_shiftedLemma6ConductorMajorant h x ε
    _ = shiftedLemma6SplitConductorMajorant h x ε :=
      shiftedLemma6ConductorMajorant_eq_split h x ε
    _ = ∑ p ∈ shiftedLemma6SplitPairRange h x ε,
        shiftedLemma6SplitPairTerm h x p :=
      shiftedLemma6SplitConductorMajorant_eq_pairSum h x ε
    _ ≤ shiftedLemma6IndependentMajorant h x ε := by
      unfold shiftedLemma6IndependentMajorant
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (shiftedLemma6SplitPairRange_subset h x ε)
      intro p hp hnot
      exact shiftedLemma6SplitPairTerm_nonneg h x p

end Chen
