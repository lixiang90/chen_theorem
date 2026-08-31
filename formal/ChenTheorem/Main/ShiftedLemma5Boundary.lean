import ChenTheorem.Main.ShiftedLemma5
import ChenTheorem.Lemma5.Boundary.Analytic

open Filter Real
open scoped Classical

namespace Chen

/-!
# Fixed-shift large smoothing boundary

The original boundary sieve used the same integer `x` both as its growing
scale and as the residue in `n (x - p₁p₂n)`.  For Theorem 2 these roles split:
the interval and prime product still grow with `x`, while the polynomial is
`n (p₁p₂n - h)`.  Modulo a divisor the latter has the same roots as
`n (h - p₁p₂n)`, so the existing local-root theory is reusable with residue
parameter `h`.
-/

def shiftedSmoothingTransitionArgument
    (h : ℕ) (q : ℕ × ℕ) (n : ℕ) : ℕ :=
  n * Nat.dist h (q.1 * q.2 * n)

noncomputable def shiftedSmoothingTransitionSiftedIndices
    (h x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothingTransitionInterval x q).filter fun n =>
    (shiftedSmoothingTransitionArgument h q n).Coprime
      (transitionSieveProduct x)

/-- Root count for the shifted transition polynomial.  Negating the second
factor does not change its zero set modulo `d`. -/
def shiftedSmoothingTransitionRootCount
    (h : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℕ :=
  smoothingTransitionRootCount h q d

theorem shiftedSmoothingBoundaryIndices_subset_transitionInterval
    (h x : ℕ) (q : ℕ × ℕ) :
    shiftedSmoothingBoundaryIndices h x q ⊆
      smoothingTransitionInterval x q := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hnSieve := Finset.mem_filter.mp hn'.1
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨hnSieve.1, hnSieve.2.1⟩
  · exact hn'.2

theorem shiftedSmoothingBoundaryLargeBase_subset_sifted
    {h x : ℕ} (hx : 1 ≤ x) (q : ℕ × ℕ) :
    (shiftedSmoothingBoundaryIndices h x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)) ⊆
      shiftedSmoothingTransitionSiftedIndices h x q := by
  intro n hn
  have hnlarge := Finset.mem_filter.mp hn
  have hnBoundary := hnlarge.1
  have hnSieve :=
    Finset.mem_filter.mp
      (Finset.mem_filter.mp hnBoundary).1
  have hrough : chenRough x (q.1 * q.2 * n - h) :=
    hnSieve.2.2.2
  apply Finset.mem_filter.mpr
  constructor
  · exact shiftedSmoothingBoundaryIndices_subset_transitionInterval
      h x q hnBoundary
  · unfold shiftedSmoothingTransitionArgument
    rw [Nat.dist_eq_sub_of_le hnSieve.2.2.1.le]
    exact (largeBase_coprime_transitionSieveProduct
      hnlarge.2).mul_left
        (chenRough_coprime_transitionSieveProduct hx hrough)

theorem shiftedSmoothingBoundaryLargeBase_inner_le_siftedCard
    {h x : ℕ} (hx : 2 ≤ x) (q : ℕ × ℕ) :
    ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)),
        ArithmeticFunction.vonMangoldt n ≤
      Real.log x *
        (shiftedSmoothingTransitionSiftedIndices h x q).card := by
  let S :=
    (shiftedSmoothingBoundaryIndices h x q).filter
      (fun n =>
        ¬(n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
  let T := shiftedSmoothingTransitionSiftedIndices h x q
  have hST : S ⊆ T :=
    shiftedSmoothingBoundaryLargeBase_subset_sifted
      (show 1 ≤ x by omega) q
  calc
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
        ∑ n ∈ S, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      apply vonMangoldt_le_log_of_mem_smoothedMIndices hx
      have hnBoundary := (Finset.mem_filter.mp hn).1
      exact
        (Finset.mem_filter.mp
          (shiftedSmoothingBoundaryIndices_subset_transitionInterval
            h x q hnBoundary)).1
    _ ≤ ∑ _n ∈ T, Real.log x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro n hnT hnS
      exact Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ x by omega))
    _ = Real.log x * T.card := by
      simp [mul_comm]

theorem shiftedSmoothingTransitionSiftedIndices_eq_indexed
    (h x : ℕ) (q : ℕ × ℕ) :
    shiftedSmoothingTransitionSiftedIndices h x q =
      indexedSiftedSet (smoothingTransitionInterval x q)
        (shiftedSmoothingTransitionArgument h q)
        (transitionSieveProduct x) := by
  rfl

theorem shiftedSmoothingTransitionSifted_card_le_lcmCount
    (h x : ℕ) (q : ℕ × ℕ) (R : ℕ) (w : ℕ → ℝ)
    (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((shiftedSmoothingTransitionSiftedIndices h x q).card : ℝ) ≤
      ∑ d₁ ∈ truncatedSieveDivisors
          (transitionSieveProduct x) R,
        ∑ d₂ ∈ truncatedSieveDivisors
            (transitionSieveProduct x) R,
          w d₁ * w d₂ *
            (((smoothingTransitionInterval x q).filter fun n =>
              d₁.lcm d₂ ∣
                shiftedSmoothingTransitionArgument h q n).card : ℝ) := by
  rw [shiftedSmoothingTransitionSiftedIndices_eq_indexed]
  calc
    ((indexedSiftedSet (smoothingTransitionInterval x q)
        (shiftedSmoothingTransitionArgument h q)
        (transitionSieveProduct x)).card : ℝ) ≤
      ∑ n ∈ smoothingTransitionInterval x q,
        (truncatedSieveDivisorSum
          (transitionSieveProduct x) R w
            (shiftedSmoothingTransitionArgument h q n)) ^ 2 :=
      indexedSifted_card_le_squareSum
        (transitionSieveProduct_ne_zero x) hR hw
    _ = _ := indexedSquareSum_eq_lcmCount
      (smoothingTransitionInterval x q)
      (shiftedSmoothingTransitionArgument h q)
      (transitionSieveProduct x) R w

/-- Divisibility by the shifted natural polynomial is equivalent to
membership in the already-developed root set with residue `h`. -/
theorem dvd_shiftedTransitionArgument_iff_mod_mem_roots
    {h x n d : ℕ} {q : ℕ × ℕ}
    (_hq : q ∈ chenPairs x) (hd : 0 < d)
    (_hn : n ∈ smoothingTransitionInterval x q) :
    d ∣ shiftedSmoothingTransitionArgument h q n ↔
      n % d ∈ smoothingTransitionRootResidues h q d := by
  let b : ℕ := q.1 * q.2 * n
  have hcastB : (b : ZMod d) =
      (q.1 : ZMod d) * (q.2 : ZMod d) * (n : ZMod d) := by
    simp only [b, Nat.cast_mul]
  constructor
  · intro hdiv
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.mod_lt n hd)
    · rw [ZMod.natCast_mod]
      have hzero :
          (n : ZMod d) * (Nat.dist h b : ZMod d) = 0 := by
        simpa only [shiftedSmoothingTransitionArgument, b,
          Nat.cast_mul] using
          (ZMod.natCast_eq_zero_iff
            (shiftedSmoothingTransitionArgument h q n) d).mpr hdiv
      rcases le_total h b with hhb | hbh
      · rw [Nat.dist_eq_sub_of_le hhb, Nat.cast_sub hhb] at hzero
        rw [hcastB] at hzero
        simp only [Nat.cast_mul] at hzero ⊢
        linear_combination -hzero
      · rw [Nat.dist_eq_sub_of_le_right hbh, Nat.cast_sub hbh] at hzero
        rw [hcastB] at hzero
        simp only [Nat.cast_mul] at hzero ⊢
        linear_combination hzero
  · intro hroot
    have hrootData := (Finset.mem_filter.mp hroot).2
    rw [ZMod.natCast_mod] at hrootData
    have hzero :
        (shiftedSmoothingTransitionArgument h q n : ZMod d) = 0 := by
      unfold shiftedSmoothingTransitionArgument
      rw [Nat.cast_mul]
      rcases le_total h b with hhb | hbh
      · rw [Nat.dist_eq_sub_of_le hhb, Nat.cast_sub hhb, hcastB]
        simp only [Nat.cast_mul] at hrootData ⊢
        linear_combination -hrootData
      · rw [Nat.dist_eq_sub_of_le_right hbh, Nat.cast_sub hbh, hcastB]
        simp only [Nat.cast_mul] at hrootData ⊢
        linear_combination hrootData
    exact (ZMod.natCast_eq_zero_iff
      (shiftedSmoothingTransitionArgument h q n) d).mp hzero

noncomputable def shiftedPositiveTransitionDivisibilityCount
    (h x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((positiveSmoothingTransitionInterval x q).filter fun n =>
    d ∣ shiftedSmoothingTransitionArgument h q n).card : ℝ)

theorem shiftedPositiveTransition_dvd_card_eq_sum_rootFibers
    {h x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    (((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ shiftedSmoothingTransitionArgument h q n).card : ℕ) =
      ∑ r ∈ smoothingTransitionRootResidues h q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
  let S := positiveSmoothingTransitionInterval x q
  let roots := smoothingTransitionRootResidues h q d
  have hfiber :=
    Finset.sum_card_fiberwise_eq_card_filter
      S roots (fun n => n % d)
  calc
    ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ shiftedSmoothingTransitionArgument h q n).card =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        n % d ∈ smoothingTransitionRootResidues h q d).card := by
      apply congrArg Finset.card
      ext n
      simp only [Finset.mem_filter]
      constructor
      · intro hn
        exact ⟨hn.1,
          (dvd_shiftedTransitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mp hn.2⟩
      · intro hn
        exact ⟨hn.1,
          (dvd_shiftedTransitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mpr hn.2⟩
    _ = ∑ r ∈ smoothingTransitionRootResidues h q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
      simpa only [S, roots] using hfiber.symm

theorem shiftedPositiveTransition_rootFiber_abs_sub_density_le
    {h x d r : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hr : r ∈ smoothingTransitionRootResidues h q d) :
    |(((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card : ℝ) -
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) / d| ≤ 3 := by
  let L := smoothingTransitionLower x q
  let U := smoothingTransitionUpper x q
  let N :=
    ((Finset.Ioc L U).filter fun n => n % d = r).card
  let Q := (U - L) / d
  have hLU : L ≤ U := smoothingTransitionLower_le_upper hq
  have hrlt : r < d :=
    Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hbounds := Ioc_modFiber_card_div_bounds hd hLU hrlt
  have hNQ : |(N : ℝ) - (Q : ℝ)| ≤ 2 := by
    have hlowR : (Q : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast hbounds.1
    have huppR : (N : ℝ) ≤ (Q : ℝ) + 2 := by
      exact_mod_cast hbounds.2
    rw [abs_le]
    constructor <;> linarith
  have hQle :
      (Q : ℝ) ≤ ((U - L : ℕ) : ℝ) / d := by
    dsimp only [Q]
    exact Nat.cast_div_le
  have hdivlt :
      ((U - L : ℕ) : ℝ) / d < (Q : ℝ) + 1 := by
    have hfloor :=
      Nat.lt_floor_add_one
        (((U - L : ℕ) : ℝ) / (d : ℝ))
    rw [Nat.floor_div_eq_div] at hfloor
    simpa only [Q, Nat.cast_add, Nat.cast_one] using hfloor
  have hQdiv :
      |(Q : ℝ) - ((U - L : ℕ) : ℝ) / d| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [positiveSmoothingTransitionInterval_eq_Ioc hq]
  change |(N : ℝ) - ((U - L : ℕ) : ℝ) / d| ≤ 3
  calc
    |(N : ℝ) - ((U - L : ℕ) : ℝ) / d| =
        |((N : ℝ) - Q) +
          ((Q : ℝ) - ((U - L : ℕ) : ℝ) / d)| := by
      congr 1
      ring
    _ ≤ |(N : ℝ) - Q| +
        |(Q : ℝ) - ((U - L : ℕ) : ℝ) / d| :=
      abs_add_le _ _
    _ ≤ 2 + 1 := add_le_add hNQ hQdiv
    _ = 3 := by norm_num

noncomputable def shiftedPositiveTransitionDivisibilityRemainder
    (h x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  shiftedPositiveTransitionDivisibilityCount h x q d -
    (shiftedSmoothingTransitionRootCount h q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

theorem abs_shiftedPositiveTransitionDivisibilityRemainder_le
    {h x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |shiftedPositiveTransitionDivisibilityRemainder h x q d| ≤
      3 * shiftedSmoothingTransitionRootCount h q d := by
  let roots := smoothingTransitionRootResidues h q d
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hcount :=
    shiftedPositiveTransition_dvd_card_eq_sum_rootFibers
      (h := h) hq hd
  have hcountR :
      shiftedPositiveTransitionDivisibilityCount h x q d =
        ∑ r ∈ roots,
          (((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) := by
    unfold shiftedPositiveTransitionDivisibilityCount
    exact_mod_cast hcount
  have hmain :
      (shiftedSmoothingTransitionRootCount h q d : ℝ) * H / d =
        ∑ _r ∈ roots, H / d := by
    unfold shiftedSmoothingTransitionRootCount
      smoothingTransitionRootCount
    simp only [roots, Finset.sum_const, nsmul_eq_mul]
    ring
  unfold shiftedPositiveTransitionDivisibilityRemainder
  rw [hcountR, hmain, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ roots,
        ((((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) - H / d)| ≤
      ∑ r ∈ roots,
        |(((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) - H / d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ roots, 3 := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [H] using
        shiftedPositiveTransition_rootFiber_abs_sub_density_le
          hq hd hr
    _ = 3 * shiftedSmoothingTransitionRootCount h q d := by
      unfold shiftedSmoothingTransitionRootCount
        smoothingTransitionRootCount
      simp only [roots, Finset.sum_const, nsmul_eq_mul]
      ring

theorem shiftedTransitionDivisibilityCount_eq_positive_add_one
    {h x d : ℕ} {q : ℕ × ℕ} :
    (((smoothingTransitionInterval x q).filter fun n =>
        d ∣ shiftedSmoothingTransitionArgument h q n).card : ℕ) =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ shiftedSmoothingTransitionArgument h q n).card + 1 := by
  let A :=
    (smoothingTransitionInterval x q).filter fun n =>
      d ∣ shiftedSmoothingTransitionArgument h q n
  let B :=
    (positiveSmoothingTransitionInterval x q).filter fun n =>
      d ∣ shiftedSmoothingTransitionArgument h q n
  have h0A : 0 ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨zero_mem_smoothingTransitionInterval x q,
      by simp [shiftedSmoothingTransitionArgument]⟩
  have herase : A.erase 0 = B := by
    ext n
    simp only [A, B, positiveSmoothingTransitionInterval,
      Finset.mem_erase, Finset.mem_filter]
    tauto
  calc
    A.card = (A.erase 0).card + 1 :=
      (Finset.card_erase_add_one h0A).symm
    _ = B.card + 1 := by rw [herase]

noncomputable def shiftedTransitionDivisibilityCount
    (h x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((smoothingTransitionInterval x q).filter fun n =>
    d ∣ shiftedSmoothingTransitionArgument h q n).card : ℝ)

noncomputable def shiftedTransitionDivisibilityRemainder
    (h x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  shiftedTransitionDivisibilityCount h x q d -
    (shiftedSmoothingTransitionRootCount h q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

theorem abs_shiftedTransitionDivisibilityRemainder_le
    {h x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |shiftedTransitionDivisibilityRemainder h x q d| ≤
      3 * shiftedSmoothingTransitionRootCount h q d + 1 := by
  have hcountNat :=
    shiftedTransitionDivisibilityCount_eq_positive_add_one
      (h := h) (x := x) (q := q) (d := d)
  have hcount :
      shiftedTransitionDivisibilityCount h x q d =
        shiftedPositiveTransitionDivisibilityCount h x q d + 1 := by
    unfold shiftedTransitionDivisibilityCount
      shiftedPositiveTransitionDivisibilityCount
    exact_mod_cast hcountNat
  have hpositive :=
    abs_shiftedPositiveTransitionDivisibilityRemainder_le
      (h := h) hq hd
  unfold shiftedTransitionDivisibilityRemainder
  rw [hcount]
  have hrearrange :
      shiftedPositiveTransitionDivisibilityCount h x q d + 1 -
          (shiftedSmoothingTransitionRootCount h q d : ℝ) *
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) / d =
        shiftedPositiveTransitionDivisibilityRemainder h x q d + 1 := by
    unfold shiftedPositiveTransitionDivisibilityRemainder
    ring
  rw [hrearrange]
  calc
    |shiftedPositiveTransitionDivisibilityRemainder h x q d + 1| ≤
        |shiftedPositiveTransitionDivisibilityRemainder h x q d| +
          |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 3 * shiftedSmoothingTransitionRootCount h q d + 1 := by
      simpa using add_le_add_right hpositive 1

theorem shiftedTransitionDivisibilityCount_eq_main_add_remainder
    (h x : ℕ) (q : ℕ × ℕ) (d : ℕ) :
    shiftedTransitionDivisibilityCount h x q d =
      (shiftedSmoothingTransitionRootCount h q d : ℝ) *
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) / d +
        shiftedTransitionDivisibilityRemainder h x q d := by
  unfold shiftedTransitionDivisibilityRemainder
  ring

noncomputable def shiftedTransitionMainQuadratic
    (h x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      w d₁ * w d₂ *
        ((shiftedSmoothingTransitionRootCount h q (d₁.lcm d₂) : ℝ) /
          (d₁.lcm d₂ : ℝ))

noncomputable def shiftedTransitionErrorQuadratic
    (h x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      |w d₁ * w d₂| *
        (3 * shiftedSmoothingTransitionRootCount h q (d₁.lcm d₂) + 1)

theorem shiftedSmoothingTransitionSifted_card_le_main_add_error
    {h x R : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (w : ℕ → ℝ) (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((shiftedSmoothingTransitionSiftedIndices h x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        shiftedTransitionMainQuadratic h x q R w +
      shiftedTransitionErrorQuadratic h x q R w := by
  let D := truncatedSieveDivisors (transitionSieveProduct x) R
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hsieve :=
    shiftedSmoothingTransitionSifted_card_le_lcmCount
      h x q R w hR hw
  calc
    ((shiftedSmoothingTransitionSiftedIndices h x q).card : ℝ) ≤
      ∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ *
          shiftedTransitionDivisibilityCount h x q (d₁.lcm d₂) := by
      simpa only [D, shiftedTransitionDivisibilityCount] using hsieve
    _ = H * shiftedTransitionMainQuadratic h x q R w +
        ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          w d₁ * w d₂ *
            shiftedTransitionDivisibilityRemainder h x q
              (d₁.lcm d₂) := by
      simp_rw [shiftedTransitionDivisibilityCount_eq_main_add_remainder,
        mul_add, Finset.sum_add_distrib]
      unfold shiftedTransitionMainQuadratic
      simp only [D]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d₁ hd₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d₂ hd₂
      ring
    _ ≤ H * shiftedTransitionMainQuadratic h x q R w +
        shiftedTransitionErrorQuadratic h x q R w := by
      apply add_le_add_right
      unfold shiftedTransitionErrorQuadratic
      simp only [D]
      apply Finset.sum_le_sum
      intro d₁ hd₁
      apply Finset.sum_le_sum
      intro d₂ hd₂
      have hd₁pos : 0 < d₁ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₁).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hd₂pos : 0 < d₂ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₂).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hlcmpos : 0 < d₁.lcm d₂ :=
        Nat.lcm_pos hd₁pos hd₂pos
      have hrem :=
        abs_shiftedTransitionDivisibilityRemainder_le
          (h := h) hq hlcmpos
      calc
        w d₁ * w d₂ *
            shiftedTransitionDivisibilityRemainder h x q
              (d₁.lcm d₂) ≤
          |w d₁ * w d₂ *
            shiftedTransitionDivisibilityRemainder h x q
              (d₁.lcm d₂)| := le_abs_self _
        _ = |w d₁ * w d₂| *
            |shiftedTransitionDivisibilityRemainder h x q
              (d₁.lcm d₂)| := abs_mul _ _
        _ ≤ |w d₁ * w d₂| *
            (3 * shiftedSmoothingTransitionRootCount h q
              (d₁.lcm d₂) + 1) :=
          mul_le_mul_of_nonneg_left hrem (abs_nonneg _)

/-- The local density for scale `x` and fixed residue `h`. -/
noncomputable def shiftedSmoothingTransitionBoundingSieve
    (h x : ℕ) (q : ℕ × ℕ) (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) : BoundingSieve where
  support := ∅
  prodPrimes := transitionSieveProduct x
  prodPrimes_squarefree := transitionSieveProduct_squarefree x
  weights := 0
  weights_nonneg := by simp
  totalMass := 0
  nu := smoothingTransitionNu h q
  nu_mult := smoothingTransitionNu_isMultiplicative h q
  nu_pos_of_prime := fun p hp hpdvd => by
    rw [smoothingTransitionNu_prime hp
      (transitionSievePrime_not_dvd_pair hx hq hp hpdvd)]
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 hp.pos
    split_ifs
    · exact div_pos (by norm_num) hpR
    · exact div_pos (by norm_num) hpR
  nu_lt_one_of_prime := fun p hp hpdvd => by
    rw [smoothingTransitionNu_prime hp
      (transitionSievePrime_not_dvd_pair hx hq hp hpdvd)]
    by_cases hph : p ∣ h
    · rw [if_pos hph]
      rw [div_lt_one (Nat.cast_pos.2 hp.pos)]
      exact_mod_cast hp.one_lt
    · rw [if_neg hph]
      have hpne : p ≠ 2 := by
        intro hp2
        subst p
        exact hph (even_iff_two_dvd.mp hhEven)
      have hptwo : 2 < p :=
        lt_of_le_of_ne hp.two_le hpne.symm
      rw [div_lt_one (Nat.cast_pos.2 hp.pos)]
      exact_mod_cast hptwo

theorem shiftedTransitionMainQuadratic_eq_mainSum_lambdaSquared
    {h x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (w : ℕ → ℝ) :
    shiftedTransitionMainQuadratic h x q R w =
      (shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq).mainSum
        (BoundingSieve.lambdaSquared
          (smoothingTruncatedWeight R w)) := by
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  unfold shiftedTransitionMainQuadratic
    shiftedSmoothingTransitionRootCount truncatedSieveDivisors
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  by_cases hd₁R : d₁ ≤ R
  · simp only [hd₁R, if_true, smoothingTruncatedWeight_of_le]
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    by_cases hd₂R : d₂ ≤ R
    · simp only [hd₂R, if_true,
        smoothingTruncatedWeight_of_le]
      have hgcd :
          d₁.gcd d₂ ∣ transitionSieveProduct x :=
        (Nat.gcd_dvd_left d₁ d₂).trans
          (Nat.dvd_of_mem_divisors hd₁)
      have hnugcd : s.nu (d₁.gcd d₂) ≠ 0 :=
        ne_of_gt (s.nu_pos_of_dvd_prodPrimes hgcd)
      have hlcm := s.nu_mult.map_lcm hnugcd
      change
        w d₁ * w d₂ * s.nu (d₁.lcm d₂) =
          s.nu d₁ * w d₁ * s.nu d₂ * w d₂ *
            (s.nu (d₁.gcd d₂))⁻¹
      rw [hlcm]
      field_simp
    · simp [hd₂R, smoothingTruncatedWeight]
  · simp [hd₁R, smoothingTruncatedWeight]

theorem shiftedTransitionMainQuadratic_eq_diagonal
    {h x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (w : ℕ → ℝ) :
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    shiftedTransitionMainQuadratic h x q R w =
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            s.nu d * smoothingTruncatedWeight R w d
          else 0) ^ 2 := by
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  rw [shiftedTransitionMainQuadratic_eq_mainSum_lambdaSquared
    hx hhEven hq]
  exact s.mainSum_lambdaSquared_eq_sum_mul_sum_sq
    (smoothingTruncatedWeight R w)

theorem shiftedTransitionErrorQuadratic_le
    (h x : ℕ) (q : ℕ × ℕ) (R : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R, |w d| ≤ 1) :
    shiftedTransitionErrorQuadratic h x q R w ≤
      ((R + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (R : ℝ) ^ 2 + 1) := by
  let D := truncatedSieveDivisors (transitionSieveProduct x) R
  let B : ℝ := 3 * (R : ℝ) ^ 2 + 1
  unfold shiftedTransitionErrorQuadratic
  change (∑ d₁ ∈ D, ∑ d₂ ∈ D,
      |w d₁ * w d₂| *
        (3 * shiftedSmoothingTransitionRootCount h q
          (d₁.lcm d₂) + 1)) ≤
    ((R + 1 : ℕ) : ℝ) ^ 2 * B
  calc
    (∑ d₁ ∈ D, ∑ d₂ ∈ D,
        |w d₁ * w d₂| *
          (3 * shiftedSmoothingTransitionRootCount h q
            (d₁.lcm d₂) + 1)) ≤
        ∑ _d₁ ∈ D, ∑ _d₂ ∈ D, B := by
      apply Finset.sum_le_sum
      intro d₁ hd₁
      apply Finset.sum_le_sum
      intro d₂ hd₂
      have hd₁R : d₁ ≤ R := (Finset.mem_filter.mp hd₁).2
      have hd₂R : d₂ ≤ R := (Finset.mem_filter.mp hd₂).2
      have hd₁pos : 0 < d₁ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₁).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hd₂pos : 0 < d₂ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₂).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hlcmle : d₁.lcm d₂ ≤ d₁ * d₂ :=
        Nat.le_of_dvd (Nat.mul_pos hd₁pos hd₂pos)
          (Nat.lcm_dvd_mul d₁ d₂)
      have hroot :
          shiftedSmoothingTransitionRootCount h q (d₁.lcm d₂) ≤
            R * R :=
        (smoothingTransitionRootCount_le h q _).trans
          (hlcmle.trans (Nat.mul_le_mul hd₁R hd₂R))
      have hweight : |w d₁ * w d₂| ≤ 1 := by
        rw [abs_mul]
        nlinarith [hw d₁ hd₁, hw d₂ hd₂,
          abs_nonneg (w d₁), abs_nonneg (w d₂)]
      have hfactor :
          3 * (shiftedSmoothingTransitionRootCount h q
              (d₁.lcm d₂) : ℝ) + 1 ≤ B := by
        dsimp only [B]
        exact_mod_cast (show
          3 * shiftedSmoothingTransitionRootCount h q (d₁.lcm d₂) + 1 ≤
            3 * R ^ 2 + 1 by
          simpa [pow_two] using
            Nat.add_le_add_right (Nat.mul_le_mul_left 3 hroot) 1)
      simpa using
        mul_le_mul hweight hfactor (by positivity) (by positivity)
    _ = (D.card : ℝ) ^ 2 * B := by
      simp [pow_two]
      ring
    _ ≤ ((R + 1 : ℕ) : ℝ) ^ 2 * B := by
      have hcard : (D.card : ℝ) ≤ (R + 1 : ℕ) := by
        exact_mod_cast truncatedSieveDivisors_card_le
          (transitionSieveProduct x) R
      have hcard0 : (0 : ℝ) ≤ D.card := by positivity
      have hR0 : (0 : ℝ) ≤ (R + 1 : ℕ) := by positivity
      have hsq : (D.card : ℝ) ^ 2 ≤
          ((R + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hsq (by
        dsimp only [B]
        positivity)

theorem abs_shiftedOptimalTransitionSelbergWeight_le
    {h x R d : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R)
    (hd : d ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R) :
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    |optimalSelbergWeight s R d| ≤
      (R : ℝ) * ((R : ℝ) + 1) := by
  dsimp only
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  change |optimalSelbergWeight s R d| ≤
    (R : ℝ) * ((R : ℝ) + 1)
  have hdP : d ∣ transitionSieveProduct x :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdR : d ≤ R := (Finset.mem_filter.mp hd).2
  have hdPs : d ∣ s.prodPrimes := by exact hdP
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdP
      (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
  have hcoeff := abs_upperMobiusCoefficient_optimal_le s hR hdP
  have hnuinv := smoothingTransitionNu_inv_le h q hdpos
  have hnupos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdPs
  rw [optimalSelbergWeight, if_pos hdPs, abs_mul,
    abs_inv, abs_of_pos hnupos]
  have hdRreal : (d : ℝ) ≤ R := by exact_mod_cast hdR
  have hcoeffnonneg :
      0 ≤ |upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d| := abs_nonneg _
  calc
    (s.nu d)⁻¹ *
        |upperMobiusCoefficient s.prodPrimes
          (optimalSelbergCoordinate s R) d| ≤
        (d : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul hnuinv hcoeff (by positivity) (by positivity)
    _ ≤ (R : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right hdRreal (by positivity)

theorem shiftedTransitionErrorQuadratic_optimalSelbergWeight_le
    {h x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    shiftedTransitionErrorQuadratic h x q R
        (optimalSelbergWeight s R) ≤
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  let K : ℝ := (R : ℝ) * ((R : ℝ) + 1)
  let w := optimalSelbergWeight s R
  let wn : ℕ → ℝ := fun d => w d / K
  have hKpos : 0 < K := by
    dsimp only [K]
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have hwn :
      ∀ d ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R, |wn d| ≤ 1 := by
    intro d hd
    have hw := abs_shiftedOptimalTransitionSelbergWeight_le
      hx hhEven hq hR hd
    change |w d / K| ≤ 1
    rw [abs_div, abs_of_pos hKpos]
    exact (div_le_one hKpos).2 (by
      simpa only [w, K, s] using hw)
  have herr := shiftedTransitionErrorQuadratic_le h x q R wn hwn
  have herrEq :
      shiftedTransitionErrorQuadratic h x q R w =
        K ^ 2 * shiftedTransitionErrorQuadratic h x q R wn := by
    unfold shiftedTransitionErrorQuadratic
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    dsimp only [wn]
    simp only [abs_mul, abs_div, abs_of_pos hKpos]
    field_simp
  change shiftedTransitionErrorQuadratic h x q R w ≤
    K ^ 2 * ((R + 1 : ℕ) : ℝ) ^ 2 *
      (3 * (R : ℝ) ^ 2 + 1)
  rw [herrEq]
  nlinarith [sq_nonneg K]

theorem shiftedTransitionMainQuadratic_optimalSelbergWeight
    {h x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    shiftedTransitionMainQuadratic h x q R
        (optimalSelbergWeight s R) =
      (truncatedSelbergMass s R)⁻¹ := by
  dsimp only
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  change shiftedTransitionMainQuadratic h x q R
      (optimalSelbergWeight s R) =
    (truncatedSelbergMass s R)⁻¹
  rw [shiftedTransitionMainQuadratic_eq_diagonal hx hhEven hq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            s.nu d * smoothingTruncatedWeight R
              (optimalSelbergWeight s R) d
          else 0) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
          (optimalSelbergCoordinate s R l) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp_rw [smoothingTruncatedWeight_optimalSelbergWeight]
      rw [optimalSelbergWeight_coordinate s R
        (Nat.dvd_of_mem_divisors hl)]
    _ = (truncatedSelbergMass s R)⁻¹ :=
      optimalSelbergCoordinate_diagonal s hR

theorem shiftedSmoothingTransitionSifted_card_le_optimal
    {h x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hhEven : Even h)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    ((shiftedSmoothingTransitionSiftedIndices h x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        (truncatedSelbergMass s R)⁻¹ +
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  have hsieve :=
    shiftedSmoothingTransitionSifted_card_le_main_add_error
      (h := h) hq
      (optimalSelbergWeight s R) hR
      (optimalSelbergWeight_one s hR)
  calc
    ((shiftedSmoothingTransitionSiftedIndices h x q).card : ℝ) ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          shiftedTransitionMainQuadratic h x q R
            (optimalSelbergWeight s R) +
          shiftedTransitionErrorQuadratic h x q R
            (optimalSelbergWeight s R) := hsieve
    _ ≤ ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s R)⁻¹ +
        ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
          ((R + 1 : ℕ) : ℝ) ^ 2 *
            (3 * (R : ℝ) ^ 2 + 1) := by
      rw [shiftedTransitionMainQuadratic_optimalSelbergWeight
        hx hhEven hq hR]
      have herr :
          shiftedTransitionErrorQuadratic h x q R
              (optimalSelbergWeight s R) ≤
            ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
              ((R + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (R : ℝ) ^ 2 + 1) := by
        simpa only [s] using
          shiftedTransitionErrorQuadratic_optimalSelbergWeight_le
            hx hhEven hq hR
      exact add_le_add le_rfl herr

/-! ### Shifted Selberg normalization -/

theorem shiftedSmoothingTransitionNu_eq_coprimeDivisorCount_div
    {h x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    smoothingTransitionNu h q l =
      coprimeDivisorCountAF h l / l := by
  have hlocal :
      ∀ p ∈ l.primeFactors,
        smoothingTransitionNu h q p =
          coprimeDivisorCountAF h p / p := by
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l := (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ transitionSieveProduct x := hpl.trans hlP
    rw [smoothingTransitionNu_prime hp
      (transitionSievePrime_not_dvd_pair hx hq hp hpP),
      coprimeDivisorCountAF_prime h hp]
  have hnu :=
    (smoothingTransitionNu_isMultiplicative h q).prod_primeFactors hlsf
  have hcount :=
    (coprimeDivisorCountAF_isMultiplicative h).prod_primeFactors hlsf
  rw [← hnu]
  calc
    ∏ p ∈ l.primeFactors, smoothingTransitionNu h q p =
        ∏ p ∈ l.primeFactors,
          coprimeDivisorCountAF h p / p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (∏ p ∈ l.primeFactors, coprimeDivisorCountAF h p) /
        ∏ p ∈ l.primeFactors, (p : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = coprimeDivisorCountAF h l / l := by
      rw [hcount, ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hlsf]

theorem shiftedCoprimeDivisorCount_div_le_selbergTerms
    {h x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hhEven : Even h) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    coprimeDivisorCountAF h l / l ≤
      (shiftedSmoothingTransitionBoundingSieve
        h x q hx hhEven hq).selbergTerms l := by
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  have hnu : s.nu l = coprimeDivisorCountAF h l / l := by
    exact shiftedSmoothingTransitionNu_eq_coprimeDivisorCount_div
      hx hq hlP hlsf
  have hnupos : 0 < s.nu l := s.nu_pos_of_dvd_prodPrimes hlP
  have hprod :
      1 ≤ ∏ p ∈ l.primeFactors, (1 - s.nu p)⁻¹ := by
    apply Finset.one_le_prod
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l := (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ s.prodPrimes := hpl.trans hlP
    have hnuppos : 0 < s.nu p := s.nu_pos_of_dvd_prodPrimes hpP
    have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hp hpP
    exact (one_le_inv₀ (sub_pos.mpr hnult)).2 (by linarith)
  rw [(s.selbergTerms_apply l), ← hnu]
  nlinarith

theorem shiftedCoprimePairHarmonic_le_truncatedSelbergMass
    {h x Y R : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hhEven : Even h) (hq : q ∈ chenPairs x)
    (hYsq : Y ^ 2 ≤ R)
    (hRcut : R ≤ transitionSieveCutoff x) :
    coprimePairHarmonic h Y ≤
      truncatedSelbergMass
        (shiftedSmoothingTransitionBoundingSieve
          h x q hx hhEven hq) R := by
  let B := squarefreeCoprimeUpTo h Y
  let A : ℕ → Finset ℕ := fun b => squarefreeCoprimeUpTo b Y
  let D := truncatedSieveDivisors (transitionSieveProduct x) R
  let T : ℕ → Finset (Finset ℕ) := fun l => allowedPrimeSubsets h l
  let source := B.sigma A
  let target := D.sigma T
  let f : (Σ _b : ℕ, ℕ) → (Σ _l : ℕ, Finset ℕ) := fun z =>
    ⟨z.1 * z.2, z.1.primeFactors⟩
  have hsource_mem {z : Σ _b : ℕ, ℕ} (hz : z ∈ source) :
      z.1 ∈ B ∧ z.2 ∈ A z.1 := Finset.mem_sigma.mp hz
  have htarget : source.image f ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    have hw' := hsource_mem hw
    have hb := Finset.mem_filter.mp hw'.1
    have hbS := Finset.mem_filter.mp hb.1
    have hbIcc := Finset.mem_Icc.mp hbS.1
    have hbSf := hbS.2
    have hbh := hb.2
    have ha := Finset.mem_filter.mp hw'.2
    have haS := Finset.mem_filter.mp ha.1
    have haIcc := Finset.mem_Icc.mp haS.1
    have haSf := haS.2
    have hab := ha.2
    have hlSf : Squarefree (w.1 * w.2) :=
      (Nat.squarefree_mul hab.symm).2 ⟨hbSf, haSf⟩
    have hlLe : w.1 * w.2 ≤ R := by
      have : w.1 * w.2 ≤ Y ^ 2 := by nlinarith
      exact this.trans hYsq
    have hlP : w.1 * w.2 ∣ transitionSieveProduct x := by
      unfold transitionSieveProduct primorial
      rw [← Nat.prod_primeFactors_of_squarefree hlSf]
      apply Finset.prod_dvd_prod_of_subset
        (w.1 * w.2).primeFactors
        ((Finset.range (transitionSieveCutoff x + 1)).filter Nat.Prime)
        id
      intro p hpL
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
      have hpl : p ∣ w.1 * w.2 :=
        (Nat.mem_primeFactors.mp hpL).2.1
      have hpLeL : p ≤ w.1 * w.2 :=
        Nat.le_of_dvd
          (Nat.mul_pos
            (Nat.zero_lt_of_lt hbIcc.1)
            (Nat.zero_lt_of_lt haIcc.1)) hpl
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        exact Nat.lt_succ_of_le
          (hpLeL.trans (hlLe.trans hRcut))
      · exact hp
    apply Finset.mem_sigma.mpr
    constructor
    · unfold D truncatedSieveDivisors
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr
          ⟨hlP, transitionSieveProduct_ne_zero x⟩, hlLe⟩
    · unfold T allowedPrimeSubsets
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_powerset]
        intro p hpb
        have hpbDvd : p ∣ w.1 :=
          (Nat.mem_primeFactors.mp hpb).2.1
        have hp := Nat.prime_of_mem_primeFactors hpb
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hpbDvd.trans (Nat.dvd_mul_right _ _),
            mul_ne_zero
              (Nat.one_le_iff_ne_zero.mp hbIcc.1)
              (Nat.one_le_iff_ne_zero.mp haIcc.1)⟩
      · intro p hpb hph
        have hp := Nat.prime_of_mem_primeFactors hpb
        have hpgcd : p ∣ w.1.gcd h := Nat.dvd_gcd
          (Nat.mem_primeFactors.mp hpb).2.1 hph
        rw [hbh] at hpgcd
        exact hp.not_dvd_one hpgcd
  have hfinj :
      ∀ a ∈ source, ∀ b ∈ source, f a = f b → a = b := by
    intro a ha b hb habEq
    have ha' := hsource_mem ha
    have hb' := hsource_mem hb
    have ha1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp ha'.1).1
    have haIcc := Finset.mem_Icc.mp ha1.1
    have hb1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp hb'.1).1
    have hpf : a.1.primeFactors = b.1.primeFactors :=
      congrArg Sigma.snd habEq
    have hfirst : a.1 = b.1 := by
      rw [← Nat.prod_primeFactors_of_squarefree ha1.2,
        ← Nat.prod_primeFactors_of_squarefree hb1.2, hpf]
    have hmul : a.1 * a.2 = b.1 * b.2 :=
      congrArg Sigma.fst habEq
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    simp only at hfirst hmul ⊢
    subst b1
    have hsecond : a2 = b2 :=
      Nat.mul_left_cancel (Nat.zero_lt_of_lt haIcc.1) hmul
    subst b2
    rfl
  have himage :
      (∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹)) =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    rw [Finset.sum_image hfinj]
  have hsubset :
      (∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹)) ≤
        ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg htarget
    intro z hzT hzI
    positivity
  have hsourceSum :
      coprimePairHarmonic h Y =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    unfold coprimePairHarmonic squarefreeCoprimeHarmonic
    change
      (∑ b ∈ B, (b : ℝ)⁻¹ * ∑ a ∈ A b, (a : ℝ)⁻¹) =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹)
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.cast_mul, mul_inv]
  have htargetMass :
      (∑ z ∈ target, ((z.1 : ℝ)⁻¹)) ≤
        truncatedSelbergMass
          (shiftedSmoothingTransitionBoundingSieve
            h x q hx hhEven hq) R := by
    let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
    unfold truncatedSelbergMass
    change (∑ z ∈ D.sigma T, ((z.1 : ℝ)⁻¹)) ≤
      ∑ l ∈ D, s.selbergTerms l
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro l hlD
    have hlP : l ∣ transitionSieveProduct x :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hlD).1
    have hlsf : Squarefree l :=
      (transitionSieveProduct_squarefree x).squarefree_of_dvd hlP
    calc
      ∑ _t ∈ T l, (l : ℝ)⁻¹ =
          ((T l).card : ℝ) * (l : ℝ)⁻¹ := by simp
      _ = coprimeDivisorCountAF h l / l := by
        rw [show T l = allowedPrimeSubsets h l by rfl,
          allowedPrimeSubsets_card hlsf]
        ring
      _ ≤ s.selbergTerms l := by
        exact shiftedCoprimeDivisorCount_div_le_selbergTerms
          hx hhEven hq hlP hlsf
  calc
    coprimePairHarmonic h Y =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := hsourceSum
    _ = ∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := hsubset
    _ ≤ truncatedSelbergMass
          (shiftedSmoothingTransitionBoundingSieve
            h x q hx hhEven hq) R := htargetMass

theorem shiftedTransitionSelbergMass_cross_lower
    {C : ℝ} (hC : 0 < C)
    (hglobal : ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100))
    {h x : ℕ} (hh0 : h ≠ 0) (hx : 1 < x) (hhEven : Even h)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    ((1 / 4) *
        Real.log (transitionSelbergHalfLevel x + 1)) ^ 2 ≤
      primeFactorEulerPenalty h *
        (C * (Real.log (transitionSelbergHalfLevel x + 2)) ^
          ((1 : ℝ) / 100)) *
        truncatedSelbergMass
          (shiftedSmoothingTransitionBoundingSieve
            h x q hx hhEven hq)
          (transitionSelbergLevel x) := by
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  have hlogH :
      (1 / 4) * Real.log (Y + 1) ≤ squarefreeHarmonic Y := by
    calc
      (1 / 4) * Real.log (Y + 1) ≤
          (1 / 4) * harmonicUpTo Y :=
        mul_le_mul_of_nonneg_left
          (log_add_one_le_harmonicUpTo Y) (by norm_num)
      _ ≤ squarefreeHarmonic Y :=
        quarter_harmonicUpTo_le_squarefreeHarmonic Y
  have hlogNonneg : 0 ≤ Real.log (Y + 1) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ Y + 1 by omega)
  have hsq :
      ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hlogNonneg) hlogH 2
  have hpair :=
    squarefreeHarmonic_sq_le_pairHarmonic
      hC hglobal (x := h) (Y := Y) hh0
  have hpairMass :=
    shiftedCoprimePairHarmonic_le_truncatedSelbergMass
      hx hhEven hq
      (transitionSelbergHalfLevel_sq_le_level
        (show 1 ≤ x by omega))
      (transitionSelbergLevel_le_cutoff
        (show 1 ≤ x by omega))
  have hfactor :
      0 ≤ primeFactorEulerPenalty h *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) := by
    apply mul_nonneg
    · unfold primeFactorEulerPenalty
      positivity
    · exact mul_nonneg hC.le
        (Real.rpow_nonneg
          (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ Y + 2 by omega))) _)
  calc
    ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 := hsq
    _ ≤ primeFactorEulerPenalty h *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            coprimePairHarmonic h Y := hpair
    _ ≤ primeFactorEulerPenalty h *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            truncatedSelbergMass s R :=
      mul_le_mul_of_nonneg_left hpairMass hfactor

/-- For every fixed positive even shift, the normalization grows with the
same logarithmic strength required by the boundary estimate.  The constant
may depend on `h`, which is exactly the quantifier order in Theorem 2. -/
theorem eventually_shiftedTransitionSelbergMass_lower
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hx : 1 < x, ∀ q, ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (shiftedSmoothingTransitionBoundingSieve
              h x q hx hhEven hq)
            (transitionSelbergLevel x) := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_global_primeFactorEulerPenalty_bound
  let a : ℝ := (1 : ℝ) / 20000
  let b : ℝ := (1 : ℝ) / 100
  let P : ℝ := primeFactorEulerPenalty h
  let c : ℝ := a ^ 2 / (32 * P * C)
  have ha : 0 < a := by
    dsimp only [a]
    norm_num
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hP : 0 < P := by
    dsimp only [P, primeFactorEulerPenalty]
    apply Finset.prod_pos
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    positivity
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, ?_⟩
  have hxlarge : ∀ᶠ x : ℕ in atTop, 2 ≤ x :=
    eventually_ge_atTop 2
  have hlogone : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 1)
  filter_upwards [hxlarge, hlogone] with x hx2 hxlog1
  intro hx q hq
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := shiftedSmoothingTransitionBoundingSieve h x q hx hhEven hq
  let L := Real.log x
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hx)
  have hYcast : (Y : ℝ) ≤ (x : ℝ) ^ a := by
    dsimp only [Y, a, transitionSelbergHalfLevel]
    exact Nat.floor_le (by positivity)
  have hxR : (1 : ℝ) ≤ x := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hrpowx : (x : ℝ) ^ a ≤ x := by
    exact Real.rpow_le_self_of_one_le hxR (by
      dsimp only [a]
      norm_num)
  have hYxR : (Y : ℝ) ≤ x := hYcast.trans hrpowx
  have hYx : Y ≤ x := by exact_mod_cast hYxR
  have hYlogUpper : Real.log (Y + 2) ≤ 2 * L := by
    have harg : (Y + 2 : ℕ) ≤ 2 * x := by omega
    have hlogmono : Real.log (Y + 2) ≤ Real.log (2 * x) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast harg
    have hlog2le : Real.log 2 ≤ L := by
      dsimp only [L]
      exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by norm_num))
        (Set.mem_Ioi.mpr (by exact_mod_cast (show 0 < x by omega)))
        (by exact_mod_cast hx2)
    calc
      Real.log (Y + 2) ≤ Real.log (2 * x) := hlogmono
      _ = Real.log 2 + L := by
        dsimp only [L]
        rw [Real.log_mul (by norm_num)
          (by exact_mod_cast (show x ≠ 0 by omega))]
      _ ≤ 2 * L := by linarith
  have hYpow :
      (Real.log (Y + 2)) ^ b ≤ 2 * L ^ b := by
    have hbase :
        (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ Y + 2 by omega))
      · exact hYlogUpper
      · exact hb.le
    have hmul : (2 * L) ^ b = (2 : ℝ) ^ b * L ^ b :=
      Real.mul_rpow (by norm_num) hL.le
    have htwo : (2 : ℝ) ^ b ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by
        dsimp only [b]
        norm_num)
    calc
      (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := hbase
      _ = (2 : ℝ) ^ b * L ^ b := hmul
      _ ≤ 2 * L ^ b :=
        mul_le_mul_of_nonneg_right htwo
          (Real.rpow_nonneg hL.le _)
  have hYlogLower : a * L ≤ Real.log (Y + 1) := by
    have hlt := rpow_lt_transitionSelbergHalfLevel_add_one x
    have hlogmono :
        Real.log ((x : ℝ) ^ a) ≤ Real.log (Y + 1) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos (by positivity) _)
      · exact Set.mem_Ioi.mpr (by positivity)
      · simpa only [Y, a] using hlt.le
    rw [Real.log_rpow (by positivity) a] at hlogmono
    simpa only [L] using hlogmono
  have hcross :=
    shiftedTransitionSelbergMass_cross_lower
      hC hglobal (h := h) hh0.ne' hx hhEven hq
  have hmassPos : 0 < truncatedSelbergMass s R := by
    apply truncatedSelbergMass_pos
    exact one_le_transitionSelbergLevel (show 1 ≤ x by omega)
  have hfactorUpper :
      P * (C * (Real.log (Y + 2)) ^ b) ≤
        2 * P * C * L ^ b := by
    calc
      P * (C * (Real.log (Y + 2)) ^ b) ≤
          P * (C * (2 * L ^ b)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hYpow hC.le) hP.le
      _ = 2 * P * C * L ^ b := by ring
  have hleftLower :
      ((a / 4) * L) ^ 2 ≤
        ((1 / 4) * Real.log (Y + 1)) ^ 2 := by
    apply pow_le_pow_left₀
    · positivity
    · calc
        (a / 4) * L = (1 / 4) * (a * L) := by ring
        _ ≤ (1 / 4) * Real.log (Y + 1) :=
          mul_le_mul_of_nonneg_left hYlogLower (by norm_num)
  have hcore :
      ((a / 4) * L) ^ 2 ≤
        (2 * P * C * L ^ b) * truncatedSelbergMass s R := by
    calc
      ((a / 4) * L) ^ 2 ≤
          ((1 / 4) * Real.log (Y + 1)) ^ 2 := hleftLower
      _ ≤ P * (C * (Real.log (Y + 2)) ^ b) *
            truncatedSelbergMass s R := by
        simpa only [Y, R, s, P, b] using hcross
      _ ≤ (2 * P * C * L ^ b) *
            truncatedSelbergMass s R :=
        mul_le_mul_of_nonneg_right hfactorUpper hmassPos.le
  have hpowIdentity :
      L ^ (2 : ℕ) = L ^ b * L ^ ((199 : ℝ) / 100) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1
    dsimp only [b]
    norm_num
  have hscaled :
      (2 * P * C * L ^ b) *
          (c * L ^ ((199 : ℝ) / 100)) ≤
        (2 * P * C * L ^ b) *
          truncatedSelbergMass s R := by
    calc
      (2 * P * C * L ^ b) *
          (c * L ^ ((199 : ℝ) / 100)) =
        ((a / 4) * L) ^ 2 := by
          dsimp only [c]
          calc
            (2 * P * C * L ^ b) *
                (a ^ 2 / (32 * P * C) *
                  L ^ ((199 : ℝ) / 100)) =
              (a ^ 2 / 16) *
                (L ^ b * L ^ ((199 : ℝ) / 100)) := by
                field_simp
                ring
            _ = (a ^ 2 / 16) * L ^ 2 := by rw [← hpowIdentity]
            _ = ((a / 4) * L) ^ 2 := by ring
      _ ≤ (2 * P * C * L ^ b) *
          truncatedSelbergMass s R := hcore
  have hcoefPos : 0 < 2 * P * C * L ^ b := by positivity
  have h199 :
      c * L ^ ((199 : ℝ) / 100) ≤
        truncatedSelbergMass s R := by
    nlinarith [hscaled]
  have h197 :
      L ^ ((197 : ℝ) / 100) ≤
        L ^ ((199 : ℝ) / 100) := by
    apply Real.rpow_le_rpow_of_exponent_le hxlog1
    norm_num
  calc
    c * (Real.log x) ^ ((197 : ℝ) / 100) =
        c * L ^ ((197 : ℝ) / 100) := by rfl
    _ ≤ c * L ^ ((199 : ℝ) / 100) :=
      mul_le_mul_of_nonneg_left h197 hc.le
    _ ≤ truncatedSelbergMass s R := h199

theorem shiftedSmoothingBoundaryLargeBase_pair_le
    {h x : ℕ} {q : ℕ × ℕ} {c : ℝ}
    (hx : 2 ≤ x) (hhEven : Even h) (hq : q ∈ chenPairs x)
    (hc : 0 < c)
    (hmass :
      c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
        truncatedSelbergMass
          (shiftedSmoothingTransitionBoundingSieve h x q
            (by omega) hhEven hq)
          (transitionSelbergLevel x)) :
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
      3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
  let s :=
    shiftedSmoothingTransitionBoundingSieve h x q (by omega) hhEven hq
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  have hR : 1 ≤ transitionSelbergLevel x :=
    one_le_transitionSelbergLevel (by omega)
  have hinner :=
    shiftedSmoothingBoundaryLargeBase_inner_le_siftedCard
      (h := h) hx q
  have hsieve :=
    shiftedSmoothingTransitionSifted_card_le_optimal
      (h := h) (x := x) (q := q) (R := transitionSelbergLevel x)
      (by omega) hhEven hq hR
  dsimp only at hsieve
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hleftPos :
      0 < c * (Real.log x) ^ ((197 : ℝ) / 100) := by
    positivity
  have hGpos :
      0 < truncatedSelbergMass s (transitionSelbergLevel x) :=
    truncatedSelbergMass_pos s hR
  have hinv :
      (truncatedSelbergMass s
          (transitionSelbergLevel x))⁻¹ ≤
        (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ :=
    (inv_le_inv₀ hGpos hleftPos).2 (by
      simpa only [s] using hmass)
  have hpairLog :=
    pairLog_inv_mul_log_le_three
      (show 1 < x by omega) hq
  have hweight0 :
      0 ≤ (Real.log
        ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
    have hY := one_lt_pairQuotient hq
    exact inv_nonneg.mpr (Real.log_nonneg hY.le)
  have hmain0 :
      0 ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s
            (transitionSelbergLevel x))⁻¹ + E := by
    dsimp only [E]
    positivity
  calc
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (shiftedSmoothingTransitionSiftedIndices h x q).card) := by
      gcongr
    _ ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E)) := by
      gcongr
    _ =
        ((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          Real.log x) *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E) := by ring
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (truncatedSelbergMass s
              (transitionSelbergLevel x))⁻¹ + E) :=
      mul_le_mul_of_nonneg_right hpairLog hmain0
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ + E) := by
      gcongr
    _ = 3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
      rfl

theorem shiftedSmoothingBoundaryLargeBaseMass_le_explicit
    {h x : ℕ} {c : ℝ} (hx : 2 ≤ x) (hhEven : Even h)
    (hc : 0 < c)
    (hmass :
      ∀ q, ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (shiftedSmoothingTransitionBoundingSieve h x q
              (by omega) hhEven hq)
            (transitionSelbergLevel x)) :
    shiftedSmoothingBoundaryLargeBaseMass h x ≤
      3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
  unfold shiftedSmoothingBoundaryLargeBaseMass
  let A : ℝ :=
    (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
              (fun n =>
                ¬(n.minFac : ℝ) ≤
                  (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
        ∑ q ∈ chenPairs x,
          3 *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) * A + E) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [A, E] using
        shiftedSmoothingBoundaryLargeBase_pair_le
          hx hhEven hq hc (hmass q hq)
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) * A +
          ((chenPairs x).card : ℝ) * E) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
      rfl

theorem eventually_shiftedSmoothingBoundaryLargeBaseMass_le
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      shiftedSmoothingBoundaryLargeBaseMass h x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨c, hc, hmass⟩ :=
    eventually_shiftedTransitionSelbergMass_lower h hh0 hhEven
  let C : ℝ := 3 * (13 * c⁻¹ + 1)
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have hpowFiveSixths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 6) (r := (2.01 : ℝ)) (by norm_num)
  have hpowNineTenths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ)) (by norm_num)
  filter_upwards [hmass, eventually_transition_width_small,
      eventually_sum_inv_primesLE_sq_le_log_rpow,
      eventually_transitionLevel_error_power_bound,
      hpowFiveSixths, hpowNineTenths,
      eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop 1)] with
      x hmass hsmall hprime herr hpowFiveSixths
        hpowNineTenths hx hL
  let L : ℝ := Real.log x
  let P : ℝ := ∑ p ∈ x.primesLE, (p : ℝ)⁻¹
  let A : ℝ := (c * L ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  let Q : ℝ := ((chenPairs x).card : ℝ)
  let T : ℝ :=
    (x : ℝ) / (Real.log x) ^ (2.01 : ℝ)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hL
  have hLone : 1 ≤ L := by
    simpa only [L, Function.comp_apply] using hL
  have hP : P ^ 2 ≤ L ^ ((1 : ℝ) / 25) := by
    simpa only [P, L] using hprime
  have hQ : Q ≤ 9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
    dsimp only [Q]
    exact chenPairs_card_cast_le x (by omega)
  have hwidth :=
    sum_smoothingTransition_width_le (x := x) hsmall
  have hexplicit :=
    shiftedSmoothingBoundaryLargeBaseMass_le_explicit
      (h := h) hx hhEven hc (fun q hq =>
        hmass (show 1 < x by omega) q hq)
  have hAeq :
      A = c⁻¹ * L ^ (-(197 : ℝ) / 100) := by
    dsimp only [A]
    rw [mul_inv, ← Real.rpow_neg hLpos.le]
    congr 2
    ring
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hAle : A ≤ c⁻¹ := by
    have hpowOne :
        1 ≤ L ^ ((197 : ℝ) / 100) :=
      Real.one_le_rpow hL (by norm_num)
    have hbase :
        c ≤ c * L ^ ((197 : ℝ) / 100) := by
      nlinarith [mul_le_mul_of_nonneg_left hpowOne hc.le]
    dsimp only [A]
    exact (inv_le_inv₀ (mul_pos hc (by positivity)) hc).2 hbase
  have hpowCombine :
      L ^ (-(0.1 : ℝ)) *
          L ^ ((1 : ℝ) / 25) *
            L ^ (-(197 : ℝ) / 100) =
        L ^ (-(203 : ℝ) / 100) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1
    norm_num
  have hlogPower :
      L ^ (-(203 : ℝ) / 100) ≤
        (L ^ (2.01 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hLpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hL
    norm_num
  have hmainShort :
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
        4 * c⁻¹ * T := by
    calc
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
          4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) *
            L ^ ((1 : ℝ) / 25) * A := by
        gcongr
      _ = 4 * c⁻¹ * (x : ℝ) *
          L ^ (-(203 : ℝ) / 100) := by
        rw [hAeq, ← hpowCombine]
        ring
      _ ≤ 4 * c⁻¹ * (x : ℝ) *
          (L ^ (2.01 : ℝ))⁻¹ := by
        gcongr
      _ = 4 * c⁻¹ * T := by
        dsimp only [T, L]
        rw [div_eq_mul_inv]
        ring
  have hcardMain : Q * A ≤ 9 * c⁻¹ * T := by
    calc
      Q * A ≤
          (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * c⁻¹ := by
        gcongr
      _ = 9 * c⁻¹ * (x : ℝ) ^ ((5 : ℝ) / 6) := by ring
      _ ≤ 9 * c⁻¹ * T := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [T]
          simpa only [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num]
            using hpowFiveSixths
        · positivity
  have herror : Q * E ≤ T := by
    have hQE : Q * E * L ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E * L ≤
            (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * E * L := by
          gcongr
        _ = E * (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := by
          dsimp only [L]
          ring
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
          simpa only [E] using herr
    have hQE0 : 0 ≤ Q * E := by
      dsimp only [Q, E]
      positivity
    have hdrop : Q * E ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E = Q * E * 1 := by ring
        _ ≤ Q * E * L := mul_le_mul_of_nonneg_left hLone hQE0
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := hQE
    have hp : (x : ℝ) ^ ((9 : ℝ) / 10) ≤ T := by
      dsimp only [T]
      simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num]
        using hpowNineTenths
    exact hdrop.trans hp
  have hwidthA :
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
        (4 * c⁻¹ + 9 * c⁻¹) * T := by
    calc
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
          (4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 + Q) *
            A := by
        gcongr
      _ = 4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A +
          Q * A := by ring
      _ ≤ 4 * c⁻¹ * T + 9 * c⁻¹ * T :=
        add_le_add hmainShort hcardMain
      _ = (4 * c⁻¹ + 9 * c⁻¹) * T := by ring
  calc
    shiftedSmoothingBoundaryLargeBaseMass h x ≤
        3 *
          ((∑ q ∈ chenPairs x,
              ((smoothingTransitionUpper x q -
                  smoothingTransitionLower x q : ℕ) : ℝ)) * A +
            Q * E) := by
      simpa only [A, E, Q, L] using hexplicit
    _ ≤ 3 * (((4 * c⁻¹ + 9 * c⁻¹) * T) + T) := by
      gcongr
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C, T]
      ring

theorem eventually_shiftedSmoothingBoundaryMass_le
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      shiftedSmoothingBoundaryMass h x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_large, hC_large, hlarge⟩ :=
    eventually_shiftedSmoothingBoundaryLargeBaseMass_le h hh0 hhEven
  let C_small : ℝ := 18 * ((Real.log 2)⁻¹ + 1)
  let C : ℝ := C_small + C_large
  have hC_small : 0 < C_small := by
    dsimp only [C_small]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨C, add_pos hC_small hC_large, ?_⟩
  filter_upwards
      [eventually_shiftedSmoothingBoundarySmallBaseMass_le h,
        hlarge] with x hsmall hlarge
  rw [shiftedSmoothingBoundaryMass_eq_small_add_large]
  calc
    shiftedSmoothingBoundarySmallBaseMass h x +
        shiftedSmoothingBoundaryLargeBaseMass h x ≤
      C_small * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) +
        C_large * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) :=
      add_le_add (by simpa only [C_small] using hsmall) hlarge
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

theorem eventually_shiftedSieveMSmoothingError_le
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      shiftedSieveMSmoothingError h x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_boundary, hC_boundary, hboundary⟩ :=
    eventually_shiftedSmoothingBoundaryMass_le h hh0 hhEven
  let C : ℝ := 19 + C_boundary
  refine ⟨C, add_pos (by norm_num) hC_boundary, ?_⟩
  have hxlogReal :
      ∀ᶠ y : ℝ in atTop, (10 : ℝ) ^ 4 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop ((10 : ℝ) ^ 4))
  have hxlog :
      ∀ᶠ x : ℕ in atTop, (10 : ℝ) ^ 4 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hxlogReal
  filter_upwards [hboundary,
    eventually_shiftedSmoothingInterior_le h,
    hxlog, eventually_gt_atTop 1] with
      x hboundary hinterior hxlog hx1
  calc
    shiftedSieveMSmoothingError h x ≤
        (x : ℝ) ^ (-(0.1 : ℝ)) * shiftedSieveM h x +
          shiftedSmoothingBoundaryMass h x :=
      shiftedSieveMSmoothingError_le_interior_add_boundary hx1 hxlog
    _ ≤ 19 * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) +
        C_boundary * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) :=
      add_le_add hinterior hboundary
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

theorem shiftedSieveM_le_smoothedSieveExpansion_add_smoothingError
    {h x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    shiftedSieveM h x ≤
      shiftedSmoothedSieveExpansion h x ε +
        shiftedSieveMSmoothingError h x := by
  rw [shiftedSieveM_eq_smoothedRoughM_add_smoothingError]
  simpa [add_comm] using
    add_le_add_right
      (shiftedSmoothedRoughM_le_smoothedSieveExpansion
        hx hε0 hεhalf) (shiftedSieveMSmoothingError h x)

end Chen
