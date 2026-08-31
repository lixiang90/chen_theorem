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

theorem shiftedLemma6PrimitiveBlock_one_eq_two
    {h x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (l : ℕ) :
    shiftedLemma6PrimitiveBlock h x 1 l =
      shiftedLemma6PrimitiveBlock h x 2 l := by
  have hfilterOne :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 1) = chenPairs x := by
    simp
  have hfilterTwo :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 2) = chenPairs x := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    have hqdata := (Finset.mem_filter.mp hq).2
    have hq₁gt : 2 < q.1 := by
      exact_mod_cast hroot.trans_lt hqdata.2.2.1
    have hq₁odd : Odd q.1 := hqdata.1.odd_of_ne_two (by omega)
    have hq₂gtq₁ : q.1 < q.2 := by
      exact_mod_cast hqdata.2.2.2.1.trans_lt hqdata.2.2.2.2.1
    have hq₂odd : Odd q.2 := hqdata.2.1.odd_of_ne_two (by omega)
    exact (hq₁odd.mul hq₂odd).coprime_two_right
  unfold shiftedLemma6PrimitiveBlock
  rw [hfilterOne, hfilterTwo]

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

noncomputable def shiftedLemma6NmTerm
    (h x : ℕ) (m l : ℕ) : ℝ :=
  lemma6LinearWeight l * ‖shiftedLemma6PrimitiveBlock h x m l‖

theorem shiftedLemma6NmTerm_nonneg (h x m l : ℕ) :
    0 ≤ shiftedLemma6NmTerm h x m l := by
  unfold shiftedLemma6NmTerm
  exact mul_nonneg (lemma6LinearWeight_nonneg l) (norm_nonneg _)

noncomputable def shiftedLemma6Nm
    (h x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ (shiftedSieveModuli h x ε).erase 1,
    shiftedLemma6NmTerm h x m l

theorem shiftedLemma6Nm_nonneg (h x : ℕ) (ε : ℝ) (m : ℕ) :
    0 ≤ shiftedLemma6Nm h x ε m := by
  unfold shiftedLemma6Nm
  apply Finset.sum_nonneg
  intro l hl
  exact shiftedLemma6NmTerm_nonneg h x m l

theorem shiftedLemma6Nm_one_eq_two
    {h x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (ε : ℝ) :
    shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2 := by
  unfold shiftedLemma6Nm shiftedLemma6NmTerm
  apply Finset.sum_congr rfl
  intro l hl
  rw [shiftedLemma6PrimitiveBlock_one_eq_two hroot l]

theorem eventually_shiftedLemma6Nm_one_eq_two
    (h : ℕ) (ε : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2 := by
  have hrootReal :
      ∀ᶠ y : ℝ in atTop, (2 : ℝ) ≤ y ^ ((1 : ℝ) / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 2)
  have hrootNat :
      ∀ᶠ x : ℕ in atTop,
        (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) :=
    tendsto_natCast_atTop_atTop.eventually hrootReal
  filter_upwards [hrootNat] with x hx
  exact shiftedLemma6Nm_one_eq_two hx ε

private theorem shifted_sum_ite_one_eq_sum_erase
    (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ S, (if l = 1 then 0 else f l) =
      ∑ l ∈ S.erase 1, f l := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases ha1 : a = 1
      · subst a
        simp [ha, ih]
      · rw [Finset.erase_insert_of_ne ha1]
        simp [ha, ha1, ih]

theorem shiftedLemma6TotientWeight_le_log_mul_linearWeight
    {h x d : ℕ} {ε : ℝ}
    (hd : d ∈ shiftedSieveModuli h x ε) (hd2 : 2 ≤ d) :
    lemma6TotientWeight d ≤
      (2 / Real.log 2) * Real.log x * lemma6LinearWeight d := by
  by_cases hdsq : Squarefree d
  · have hdx : d ≤ x := by
      have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
      omega
    have hratio := (totient_ratio_le_card_succ hdsq).trans
      (primeFactors_card_succ_le_log hdsq hd2)
    have hlog : Real.log d ≤ Real.log x := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hdx)
    have hconst : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
    have hratio' : (d : ℝ) / (Nat.totient d : ℝ) ≤
        (2 / Real.log 2) * Real.log x :=
      hratio.trans (mul_le_mul_of_nonneg_left hlog hconst)
    have htotpos : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    unfold lemma6TotientWeight lemma6LinearWeight
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d * (Nat.totient d : ℝ)⁻¹ =
          ((d : ℝ) / (Nat.totient d : ℝ)) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        field_simp
      _ ≤ ((2 / Real.log 2) * Real.log x) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right hratio'
        positivity
      _ = (2 / Real.log 2) * Real.log x *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by ring
  · unfold lemma6TotientWeight lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
    norm_num

theorem shiftedLemma6_inner_sum_le_nm
    {h x m : ℕ} {ε : ℝ} :
    (∑ l ∈ shiftedSieveModuli h x ε,
        if l = 1 then 0
        else lemma6TotientWeight l *
          ‖shiftedLemma6PrimitiveBlock h x m l‖) ≤
      (2 / Real.log 2) * Real.log x * shiftedLemma6Nm h x ε m := by
  rw [shifted_sum_ite_one_eq_sum_erase]
  unfold shiftedLemma6Nm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlmem : l ∈ shiftedSieveModuli h x ε :=
    Finset.mem_of_mem_erase hl
  have hl2 : 2 ≤ l := by
    have hlne : l ≠ 1 := Finset.ne_of_mem_erase hl
    have hlpos := (Finset.mem_filter.mp hlmem).2.1
    omega
  unfold shiftedLemma6NmTerm
  calc
    lemma6TotientWeight l *
        ‖shiftedLemma6PrimitiveBlock h x m l‖ ≤
      ((2 / Real.log 2) * Real.log x * lemma6LinearWeight l) *
        ‖shiftedLemma6PrimitiveBlock h x m l‖ := by
      exact mul_le_mul_of_nonneg_right
        (shiftedLemma6TotientWeight_le_log_mul_linearWeight hlmem hl2)
        (norm_nonneg _)
    _ = (2 / Real.log 2) * Real.log x *
        (lemma6LinearWeight l *
          ‖shiftedLemma6PrimitiveBlock h x m l‖) := by ring

private noncomputable def shiftedInvNatTwist
    (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else f n / (n : ℝ)
  map_zero' := if_pos rfl

@[simp] private theorem shiftedInvNatTwist_apply
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    shiftedInvNatTwist f n =
      if n = 0 then 0 else f n / (n : ℝ) := rfl

private theorem shiftedInvNatTwist_mul
    (f g : ArithmeticFunction ℝ) :
    shiftedInvNatTwist (f * g) =
      shiftedInvNatTwist f * shiftedInvNatTwist g := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  change
    (if n = 0 then 0 else
      (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) / (n : ℝ)) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 = 0 then 0 else f p.1 / (p.1 : ℝ)) *
          (if p.2 = 0 then 0 else g p.2 / (p.2 : ℝ))
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
    have hp₁ : p.1 ≠ 0 :=
      Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hp₂ : p.2 ≠ 0 :=
      Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    simp only [hp₁, hp₂, if_false]
    rw [← hpdata.1]
    push_cast
    field_simp

private theorem shiftedPartialSum_mul_le_mul
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (f * g) n ≤
      (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
  calc
    ∑ p ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter
        (fun p => p.1 * p.2 ≤ N), f p.1 * g p.2 ≤
      ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N,
        f p.1 * g p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro p hp hnot
      exact mul_nonneg (hf p.1) (hg p.2)
    _ = (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

private theorem shiftedInvNatTwist_zeta_nonneg (n : ℕ) :
    0 ≤ shiftedInvNatTwist
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : n = 0
  · simp [shiftedInvNatTwist, hn]
  · simp [shiftedInvNatTwist, hn, ArithmeticFunction.zeta_apply]

private theorem sum_shiftedInvNatTwist_zeta (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        shiftedInvNatTwist
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n =
      (harmonic N : ℝ) := by
  have hfin : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp
    omega
  rw [hfin, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  simp [shiftedInvNatTwist, hnpos.ne',
    ArithmeticFunction.zeta_apply, Rat.cast_inv, Rat.cast_natCast]

private theorem sum_shiftedInvNatTwist_zeta_cube_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((shiftedInvNatTwist
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) n ≤
      (harmonic N : ℝ) ^ 3 := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hz : ∀ n, 0 ≤ z n := shiftedInvNatTwist_zeta_nonneg
  have hzz : ∀ n, 0 ≤ (z * z) n := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hz p.1) (hz p.2)
  calc
    ∑ n ∈ Finset.Ioc 0 N, (z ^ 3) n =
        ∑ n ∈ Finset.Ioc 0 N, ((z * z) * z) n := by
      rw [pow_succ, pow_two]
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (z * z) n) *
        ∑ n ∈ Finset.Ioc 0 N, z n :=
      shiftedPartialSum_mul_le_mul (z * z) z hzz hz N
    _ ≤ ((∑ n ∈ Finset.Ioc 0 N, z n) *
        ∑ n ∈ Finset.Ioc 0 N, z n) *
          ∑ n ∈ Finset.Ioc 0 N, z n := by
      apply mul_le_mul_of_nonneg_right
        (shiftedPartialSum_mul_le_mul z z hz hz N)
      exact Finset.sum_nonneg fun n hn => hz n
    _ = (harmonic N : ℝ) ^ 3 := by
      rw [show ∑ n ∈ Finset.Ioc 0 N, z n =
          (harmonic N : ℝ) by exact sum_shiftedInvNatTwist_zeta N]
      ring

private theorem shifted_zeta_cube_apply_squarefree_real
    {d : ℕ} (hd : Squarefree d) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      (3 : ℝ) ^ d.primeFactors.card := by
  have hnat :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) d =
        3 ^ d.primeFactors.card := by
    rw [show (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3 =
        ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta by
      have hz :
          (ArithmeticFunction.zeta : ArithmeticFunction ℕ) *
              ArithmeticFunction.zeta = ArithmeticFunction.sigma 0 := by
        simpa only [ArithmeticFunction.pow_zero_eq_zeta] using
          (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 0))
      rw [pow_succ, pow_two, hz]]
    rw [← ArithmeticFunction.isMultiplicative_sigma.prodPrimeFactors_add_of_squarefree
      ArithmeticFunction.isMultiplicative_zeta hd]
    rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hs := ArithmeticFunction.sigma_zero_apply_prime_pow
      (i := 1) hpprime
    norm_num at hs
    rw [ArithmeticFunction.add_apply, hs]
    simp [ArithmeticFunction.zeta_apply, hpprime.ne_zero]
  have hcoe :
      (↑((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) :
          ArithmeticFunction ℝ) =
        (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ) ^ 3 := by
    rw [pow_succ, pow_two, pow_succ, pow_two,
      ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_mul]
  rw [← hcoe]
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
  simpa only [ArithmeticFunction.natCoe_apply, Nat.cast_pow,
    Nat.cast_ofNat] using hcast

private theorem shiftedInvNatTwist_zeta_cube_eq (d : ℕ) :
    shiftedInvNatTwist
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      ((shiftedInvNatTwist
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  congr 1
  rw [pow_succ, pow_two, shiftedInvNatTwist_mul,
    shiftedInvNatTwist_mul, pow_succ, pow_two]

private theorem shiftedInvNatTwist_zeta_cube_nonneg (d : ℕ) :
    0 ≤ ((shiftedInvNatTwist
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  change 0 ≤ (z ^ 3) d
  rw [pow_succ, pow_two, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (shiftedInvNatTwist_zeta_nonneg q.1)
      (shiftedInvNatTwist_zeta_nonneg q.2)
  · exact shiftedInvNatTwist_zeta_nonneg p.2

private theorem shiftedLemma6LinearWeight_le_cube (d : ℕ) :
    lemma6LinearWeight d ≤
      ((shiftedInvNatTwist
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    rw [← shiftedInvNatTwist_zeta_cube_eq]
    unfold lemma6LinearWeight distinctPrimeFactors
    rw [shiftedInvNatTwist_apply, if_neg hd0,
      shifted_zeta_cube_apply_squarefree_real hd]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs,
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
      norm_num
    rw [hmu, one_mul]
  · unfold lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
    exact shiftedInvNatTwist_zeta_cube_nonneg d

theorem sum_shiftedSieveModuli_lemma6LinearWeight_le
    (h x : ℕ) (ε : ℝ) :
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d ≤
      (harmonic x : ℝ) ^ 3 := by
  let z := shiftedInvNatTwist
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hsubset : shiftedSieveModuli h x ε ⊆ Finset.Ioc 0 x := by
    intro d hd
    rw [shiftedSieveModuli, Finset.mem_filter] at hd
    rw [Finset.mem_Ioc]
    have hdrange : d < x + 1 := Finset.mem_range.mp hd.1
    exact ⟨by omega, by omega⟩
  calc
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d ≤
        ∑ d ∈ shiftedSieveModuli h x ε, (z ^ 3) d := by
      apply Finset.sum_le_sum
      intro d hd
      exact shiftedLemma6LinearWeight_le_cube d
    _ ≤ ∑ d ∈ Finset.Ioc 0 x, (z ^ 3) d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd hnot
      exact shiftedInvNatTwist_zeta_cube_nonneg d
    _ ≤ (harmonic x : ℝ) ^ 3 :=
      sum_shiftedInvNatTwist_zeta_cube_le x

theorem sum_shiftedSieveModuli_lemma6TotientWeight_le
    {h x : ℕ} (hx2 : 2 ≤ x) (ε : ℝ) :
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
      1 + (2 / Real.log 2) * Real.log x *
        (harmonic x : ℝ) ^ 3 := by
  calc
    ∑ d ∈ shiftedSieveModuli h x ε, lemma6TotientWeight d ≤
        1 + ∑ d ∈ (shiftedSieveModuli h x ε).erase 1,
          lemma6TotientWeight d := by
      by_cases h1 : 1 ∈ shiftedSieveModuli h x ε
      · rw [← Finset.add_sum_erase _ _ h1]
        simp [lemma6TotientWeight, distinctPrimeFactors]
      · rw [Finset.erase_eq_self.mpr h1]
        linarith
    _ ≤ 1 + ∑ d ∈ (shiftedSieveModuli h x ε).erase 1,
          ((2 / Real.log 2) * Real.log x) * lemma6LinearWeight d := by
      gcongr with d hd
      exact shiftedLemma6TotientWeight_le_log_mul_linearWeight
        (Finset.mem_of_mem_erase hd) (by
          have hdne := Finset.ne_of_mem_erase hd
          have hdpos :=
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).2.1
          omega)
    _ ≤ 1 + ((2 / Real.log 2) * Real.log x) *
          ∑ d ∈ shiftedSieveModuli h x ε, lemma6LinearWeight d := by
      rw [Finset.mul_sum]
      apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _)
      intro d hd hnot
      exact mul_nonneg (by
        have hx1 : 1 ≤ x := by omega
        have : (0 : ℝ) ≤ Real.log x :=
          Real.log_nonneg (by exact_mod_cast hx1)
        positivity) (lemma6LinearWeight_nonneg d)
    _ ≤ 1 + (2 / Real.log 2) * Real.log x *
          (harmonic x : ℝ) ^ 3 := by
      gcongr
      exact sum_shiftedSieveModuli_lemma6LinearWeight_le h x ε

theorem shiftedSieveModuli_mem_lemma6MRange
    {h x m : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (hm : m ∈ shiftedSieveModuli h x ε) (hm1 : m ≠ 1) :
    m ∈ lemma6MRange x := by
  rw [mem_lemma6MRange]
  have hmdata := Finset.mem_filter.mp hm
  have hmpos : 1 ≤ m := hmdata.2.1
  have hmx : m ≤ x := by
    have := Finset.mem_range.mp hmdata.1
    omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  refine ⟨by omega, hmx, ?_⟩
  calc
    (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hmdata.2.2.2
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hxR (by linarith)

theorem shiftedLemma6IndependentMajorant_le_nm_bound
    {h x : ℕ} {ε M : ℝ} (hx4 : 4 ≤ x) (hε : 0 ≤ ε)
    (hone : shiftedLemma6Nm h x ε 1 = shiftedLemma6Nm h x ε 2)
    (hM : ∀ m ∈ lemma6MRange x, shiftedLemma6Nm h x ε m ≤ M) :
    shiftedLemma6IndependentMajorant h x ε ≤
      (∑ m ∈ shiftedSieveModuli h x ε, lemma6TotientWeight m) *
        ((2 / Real.log 2) * Real.log x * M) := by
  have hx1 : 1 ≤ x := by omega
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hfactor0 : 0 ≤ (2 / Real.log 2) * Real.log x := by
    positivity
  have hNmAll : ∀ m ∈ shiftedSieveModuli h x ε,
      shiftedLemma6Nm h x ε m ≤ M := by
    intro m hm
    by_cases hm1 : m = 1
    · subst m
      rw [hone]
      exact hM 2 (two_mem_lemma6MRange hx4)
    · exact hM m
        (shiftedSieveModuli_mem_lemma6MRange hx1 hε hm hm1)
  rw [shiftedLemma6IndependentMajorant_eq_bisum]
  calc
    ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          (∑ l ∈ shiftedSieveModuli h x ε,
            if l = 1 then 0
            else lemma6TotientWeight l *
              ‖shiftedLemma6PrimitiveBlock h x m l‖) ≤
      ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ((2 / Real.log 2) * Real.log x *
            shiftedLemma6Nm h x ε m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left shiftedLemma6_inner_sum_le_nm
        (lemma6TotientWeight_nonneg m)
    _ ≤ ∑ m ∈ shiftedSieveModuli h x ε,
        lemma6TotientWeight m *
          ((2 / Real.log 2) * Real.log x * M) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left (hNmAll m hm) hfactor0
      · exact lemma6TotientWeight_nonneg m
    _ = (∑ m ∈ shiftedSieveModuli h x ε,
          lemma6TotientWeight m) *
        ((2 / Real.log 2) * Real.log x * M) := by
      rw [Finset.sum_mul]

end Chen
