import ChenTheorem.Lemma5.Smoothing
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve

namespace Chen

open scoped Classical

noncomputable def transitionSieveCutoff (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 100)⌋₊

noncomputable def transitionSieveProduct (x : ℕ) : ℕ :=
  primorial (transitionSieveCutoff x)

theorem transitionSieveProduct_squarefree (x : ℕ) :
    Squarefree (transitionSieveProduct x) := by
  unfold transitionSieveProduct primorial
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2).2 hpq
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.squarefree

theorem transitionSieveProduct_ne_zero (x : ℕ) :
    transitionSieveProduct x ≠ 0 :=
  (transitionSieveProduct_squarefree x).ne_zero

theorem prime_le_transitionThreshold_of_dvd
    {x p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
  have hpcut : p ≤ transitionSieveCutoff x := by
    exact hp.dvd_primorial_iff.mp hpdvd
  calc
    (p : ℝ) ≤ transitionSieveCutoff x := by exact_mod_cast hpcut
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

theorem largeBase_coprime_transitionSieveProduct
    {x n : ℕ}
    (hlarge :
      ¬(n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    n.Coprime (transitionSieveProduct x) := by
  rw [Nat.coprime_comm]
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpn
  have hmin : n.minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpn
  have hpbound :=
    prime_le_transitionThreshold_of_dvd hp hpdvd
  apply hlarge
  have hminR : (n.minFac : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hmin
  exact hminR.trans hpbound

theorem chenRough_coprime_transitionSieveProduct
    {x a : ℕ} (hx : 1 ≤ x) (hrough : chenRough x a) :
    a.Coprime (transitionSieveProduct x) := by
  rw [Nat.coprime_comm]
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpa
  apply hrough p hp
  · have hpone :
        (x : ℝ) ^ ((1 : ℝ) / 100) ≤
          (x : ℝ) ^ ((1 : ℝ) / 4) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hx) (by norm_num)
    exact (prime_le_transitionThreshold_of_dvd hp hpdvd).trans hpone
  · exact hpa

/-- The unsifted transition interval; unlike `smoothingBoundaryIndices`,
this drops the roughness condition so that congruence classes can be counted
directly. -/
noncomputable def smoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothedMIndices x q).filter fun n =>
    (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))

/-- The dimension-two polynomial used in the transition sieve. -/
def smoothingTransitionArgument
    (x : ℕ) (q : ℕ × ℕ) (n : ℕ) : ℕ :=
  n * (x - q.1 * q.2 * n)

/-- The part of the transition interval surviving the small-prime
dimension-two sieve. -/
noncomputable def smoothingTransitionSiftedIndices
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothingTransitionInterval x q).filter fun n =>
    (smoothingTransitionArgument x q n).Coprime
      (transitionSieveProduct x)

theorem smoothingBoundaryIndices_subset_transitionInterval
    (x : ℕ) (q : ℕ × ℕ) :
    smoothingBoundaryIndices x q ⊆
      smoothingTransitionInterval x q := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hnSieve := Finset.mem_filter.mp hn'.1
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨hnSieve.1, hnSieve.2.1⟩
  · exact hn'.2

theorem smoothingBoundaryLargeBase_subset_sifted
    {x : ℕ} (hx : 1 ≤ x) (q : ℕ × ℕ) :
    (smoothingBoundaryIndices x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)) ⊆
      smoothingTransitionSiftedIndices x q := by
  intro n hn
  have hnlarge := Finset.mem_filter.mp hn
  have hnBoundary := hnlarge.1
  have hnSieve :=
    Finset.mem_filter.mp
      (Finset.mem_filter.mp hnBoundary).1
  have hrough : chenRough x (x - q.1 * q.2 * n) :=
    hnSieve.2.2
  apply Finset.mem_filter.mpr
  constructor
  · exact smoothingBoundaryIndices_subset_transitionInterval
      x q hnBoundary
  · unfold smoothingTransitionArgument
    exact (largeBase_coprime_transitionSieveProduct
      hnlarge.2).mul_left
        (chenRough_coprime_transitionSieveProduct hx hrough)

theorem vonMangoldt_le_log_of_mem_smoothedMIndices
    {x n : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hn : n ∈ smoothedMIndices x q) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
  have hnrange : n < x + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  by_cases hn0 : n = 0
  · simp [hn0, hlog0]
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr
          (by exact_mod_cast Nat.pos_of_ne_zero hn0))
        (Set.mem_Ioi.mpr
          (by exact_mod_cast (by omega : 0 < x)))
        (by exact_mod_cast (by omega : n ≤ x)))

theorem smoothingBoundaryLargeBase_inner_le_siftedCard
    {x : ℕ} (hx : 2 ≤ x) (q : ℕ × ℕ) :
    ∑ n ∈ (smoothingBoundaryIndices x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)),
        ArithmeticFunction.vonMangoldt n ≤
      Real.log x *
        (smoothingTransitionSiftedIndices x q).card := by
  let S :=
    (smoothingBoundaryIndices x q).filter
      (fun n =>
        ¬(n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
  let T := smoothingTransitionSiftedIndices x q
  have hST : S ⊆ T :=
    smoothingBoundaryLargeBase_subset_sifted
      (show 1 ≤ x by omega) q
  calc
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
        ∑ n ∈ S, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      apply vonMangoldt_le_log_of_mem_smoothedMIndices hx
      have hnBoundary :=
        (Finset.mem_filter.mp hn).1
      exact
        (Finset.mem_filter.mp
          (smoothingBoundaryIndices_subset_transitionInterval
            x q hnBoundary)).1
    _ ≤ ∑ _n ∈ T, Real.log x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro n hnT hnS
      exact Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ x by omega))
    _ = Real.log x * T.card := by
      simp [mul_comm]

/-! ### A finite truncated Selberg sieve for an indexed polynomial -/

/-- Divisors of `P` retained at Selberg level `R`. -/
def truncatedSieveDivisors (P R : ℕ) : Finset ℕ :=
  P.divisors.filter fun d => d ≤ R

/-- A general truncated divisor sum.  It is stated independently of the
transition polynomial so its square expansion can be reused. -/
noncomputable def truncatedSieveDivisorSum
    (P R : ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ truncatedSieveDivisors P R,
    if d ∣ a then w d else 0

theorem one_mem_truncatedSieveDivisors
    {P R : ℕ} (hP : P ≠ 0) (hR : 1 ≤ R) :
    1 ∈ truncatedSieveDivisors P R := by
  simp [truncatedSieveDivisors, hP, hR]

/-- On an integer coprime to the prime product, a truncated divisor sum
whose first coefficient is one equals one. -/
theorem truncatedSieveDivisorSum_eq_one_of_coprime
    {P R a : ℕ} {w : ℕ → ℝ}
    (hP : P ≠ 0) (hR : 1 ≤ R) (hw : w 1 = 1)
    (ha : a.Coprime P) :
    truncatedSieveDivisorSum P R w a = 1 := by
  unfold truncatedSieveDivisorSum
  let D := truncatedSieveDivisors P R
  have h1D : 1 ∈ D :=
    one_mem_truncatedSieveDivisors hP hR
  calc
    ∑ d ∈ truncatedSieveDivisors P R,
        (if d ∣ a then w d else 0) =
      ∑ d ∈ D, (if d ∣ a then w d else 0) := by rfl
    _ = if 1 ∣ a then w 1 else 0 := by
      apply Finset.sum_eq_single 1
      · intro d hdD hd1
        have hdP : d ∣ P :=
          Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hdD).1
        by_cases hda : d ∣ a
        · have hdgcd : d ∣ Nat.gcd a P :=
            Nat.dvd_gcd hda hdP
          have hdOne : d ∣ 1 := by
            simpa [ha] using hdgcd
          exact (hd1 (Nat.dvd_one.mp hdOne)).elim
        · simp [hda]
      · intro hnot
        exact (hnot h1D).elim
    _ = 1 := by simp [hw]

/-- Indexed sifted set for an arbitrary finite family and arithmetic
argument. -/
def indexedSiftedSet
    (S : Finset ℕ) (F : ℕ → ℕ) (P : ℕ) : Finset ℕ :=
  S.filter fun n => (F n).Coprime P

/-- The elementary pointwise Λ² upper-bound sieve inequality. -/
theorem indexedSifted_card_le_squareSum
    {S : Finset ℕ} {F : ℕ → ℕ} {P R : ℕ}
    {w : ℕ → ℝ}
    (hP : P ≠ 0) (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((indexedSiftedSet S F P).card : ℝ) ≤
      ∑ n ∈ S, (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
  let T := indexedSiftedSet S F P
  have hTS : T ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  calc
    (T.card : ℝ) = ∑ _n ∈ T, (1 : ℝ) := by simp
    _ = ∑ n ∈ T,
          (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hcop := (Finset.mem_filter.mp hn).2
      rw [truncatedSieveDivisorSum_eq_one_of_coprime
        hP hR hw hcop]
      norm_num
    _ ≤ ∑ n ∈ S,
          (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hTS
      intro n hnS hnT
      exact sq_nonneg _

/-- Exact lcm expansion of the indexed square sieve. -/
theorem indexedSquareSum_eq_lcmCount
    (S : Finset ℕ) (F : ℕ → ℕ)
    (P R : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ S, (truncatedSieveDivisorSum P R w (F n)) ^ 2 =
      ∑ d₁ ∈ truncatedSieveDivisors P R,
        ∑ d₂ ∈ truncatedSieveDivisors P R,
          w d₁ * w d₂ *
            ((S.filter fun n => d₁.lcm d₂ ∣ F n).card : ℝ) := by
  unfold truncatedSieveDivisorSum
  rw [Finset.sum_comm]
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  calc
    ∑ n ∈ S,
        (if d₁ ∣ F n then w d₁ else 0) *
          (if d₂ ∣ F n then w d₂ else 0) =
      ∑ n ∈ S,
        w d₁ * w d₂ *
          (if d₁.lcm d₂ ∣ F n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h₁ : d₁ ∣ F n
      · by_cases h₂ : d₂ ∣ F n
        · simp [h₁, h₂, Nat.lcm_dvd h₁ h₂]
        · have hnot : ¬d₁.lcm d₂ ∣ F n := by
            intro h
            exact h₂ (Nat.dvd_trans
              (Nat.dvd_lcm_right d₁ d₂) h)
          simp [h₁, h₂, hnot]
      · have hnot : ¬d₁.lcm d₂ ∣ F n := by
          intro h
          exact h₁ (Nat.dvd_trans
            (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h₁, hnot]
    _ = w d₁ * w d₂ *
        ∑ n ∈ S,
          (if d₁.lcm d₂ ∣ F n then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
    _ = w d₁ * w d₂ *
        ((S.filter fun n => d₁.lcm d₂ ∣ F n).card : ℝ) := by
      congr 1
      rw [← Finset.sum_filter]
      simp
    _ = w d₂ * w d₁ *
        ((S.filter fun n => d₂.lcm d₁ ∣ F n).card : ℝ) := by
      rw [Nat.lcm_comm]
      ring

theorem smoothingTransitionSiftedIndices_eq_indexed
    (x : ℕ) (q : ℕ × ℕ) :
    smoothingTransitionSiftedIndices x q =
      indexedSiftedSet (smoothingTransitionInterval x q)
        (smoothingTransitionArgument x q)
        (transitionSieveProduct x) := by
  rfl

/-- The transition count is reduced exactly to lcm-divisibility counts.
The remaining choice of `w` is the analytic Selberg optimization. -/
theorem smoothingTransitionSifted_card_le_lcmCount
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ) (w : ℕ → ℝ)
    (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ∑ d₁ ∈ truncatedSieveDivisors
          (transitionSieveProduct x) R,
        ∑ d₂ ∈ truncatedSieveDivisors
            (transitionSieveProduct x) R,
          w d₁ * w d₂ *
            (((smoothingTransitionInterval x q).filter fun n =>
              d₁.lcm d₂ ∣
                smoothingTransitionArgument x q n).card : ℝ) := by
  rw [smoothingTransitionSiftedIndices_eq_indexed]
  calc
    ((indexedSiftedSet (smoothingTransitionInterval x q)
        (smoothingTransitionArgument x q)
        (transitionSieveProduct x)).card : ℝ) ≤
      ∑ n ∈ smoothingTransitionInterval x q,
        (truncatedSieveDivisorSum
          (transitionSieveProduct x) R w
            (smoothingTransitionArgument x q n)) ^ 2 :=
      indexedSifted_card_le_squareSum
        (transitionSieveProduct_ne_zero x) hR hw
    _ = _ := indexedSquareSum_eq_lcmCount
      (smoothingTransitionInterval x q)
      (smoothingTransitionArgument x q)
      (transitionSieveProduct x) R w

/-! ### Local roots of the transition polynomial -/

/-- Residue classes modulo `d` on which
`r (x - p₁p₂ r)` vanishes.  The expression is evaluated in `ZMod d`, so
there is no truncated-natural-subtraction issue. -/
def smoothingTransitionRootResidues
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun r =>
    (r : ZMod d) *
      ((x : ZMod d) -
        (q.1 * q.2 : ℕ) * (r : ZMod d)) = 0

def smoothingTransitionRootCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℕ :=
  (smoothingTransitionRootResidues x q d).card

/-- The same local roots represented intrinsically in `ZMod d`. -/
noncomputable def smoothingTransitionZModRoots
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) [NeZero d] :
    Finset (ZMod d) :=
  Finset.univ.filter fun r =>
    r * ((x : ZMod d) -
      (q.1 * q.2 : ℕ) * r) = 0

theorem smoothingTransitionRootResidues_image_eq_zmodRoots
    {x d : ℕ} {q : ℕ × ℕ} (hd : 0 < d) :
    letI : NeZero d := ⟨hd.ne'⟩
    (smoothingTransitionRootResidues x q d).image
        (fun r : ℕ => (r : ZMod d)) =
      smoothingTransitionZModRoots x q d := by
  letI : NeZero d := ⟨hd.ne'⟩
  ext z
  simp only [Finset.mem_image, smoothingTransitionRootResidues,
    smoothingTransitionZModRoots, Finset.mem_filter,
    Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, ⟨hrlt, hrroot⟩, rfl⟩
    exact hrroot
  · intro hz
    refine ⟨z.val, ⟨z.val_lt, ?_⟩, ?_⟩
    · simpa only [ZMod.natCast_zmod_val] using hz
    · exact ZMod.natCast_zmod_val z

theorem smoothingTransitionRootCount_eq_zmodRoots_card
    {x d : ℕ} {q : ℕ × ℕ} (hd : 0 < d) :
    letI : NeZero d := ⟨hd.ne'⟩
    smoothingTransitionRootCount x q d =
      (smoothingTransitionZModRoots x q d).card := by
  letI : NeZero d := ⟨hd.ne'⟩
  have himage :=
    smoothingTransitionRootResidues_image_eq_zmodRoots
      (x := x) (q := q) hd
  have hinj : Set.InjOn
      (fun r : ℕ => (r : ZMod d))
      (smoothingTransitionRootResidues x q d : Set ℕ) := by
    intro r hr s hs hrs
    have hrlt : r < d :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < d :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val hrs
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  unfold smoothingTransitionRootCount
  calc
    (smoothingTransitionRootResidues x q d).card =
        ((smoothingTransitionRootResidues x q d).image
          (fun r : ℕ => (r : ZMod d))).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (smoothingTransitionZModRoots x q d).card := by
      rw [himage]

/-- Over a prime modulus not dividing `p₁p₂`, the roots are exactly zero
and `(p₁p₂)⁻¹x`. -/
theorem smoothingTransitionRootResidues_image_prime
    {x p : ℕ} {q : ℕ × ℕ} (hp : p.Prime)
    (hpb : ¬p ∣ q.1 * q.2) :
    (smoothingTransitionRootResidues x q p).image
        (fun r : ℕ => (r : ZMod p)) =
      {0, ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
        (x : ZMod p)} := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpb₁ : ¬p ∣ q.1 := fun h =>
    hpb (dvd_mul_of_dvd_left h q.2)
  have hpb₂ : ¬p ∣ q.2 := fun h =>
    hpb (dvd_mul_of_dvd_right h q.1)
  have hbZ :
      (q.1 : ZMod p) * (q.2 : ZMod p) ≠ 0 := by
    exact mul_ne_zero
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₁)
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₂)
  ext z
  simp only [Finset.mem_image, smoothingTransitionRootResidues,
    Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, ⟨hrlt, hrroot⟩, rfl⟩
    rw [mul_eq_zero] at hrroot
    rcases hrroot with hr | hr
    · exact Or.inl hr
    · right
      rw [eq_inv_mul_iff_mul_eq₀ hbZ]
      simpa [Nat.cast_mul, mul_assoc] using
        (sub_eq_zero.mp hr).symm
  · intro hz
    let c : ZMod p :=
      ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
        (x : ZMod p)
    rcases hz with hz | hz
    · refine ⟨0, ⟨hp.pos, by simp⟩, ?_⟩
      simpa using hz.symm
    · refine ⟨c.val, ?_, ?_⟩
      · constructor
        · exact c.val_lt
        · rw [ZMod.natCast_zmod_val, mul_eq_zero]
          right
          apply sub_eq_zero.mpr
          dsimp only [c]
          rw [Nat.cast_mul, ← mul_assoc,
            mul_inv_cancel₀ hbZ, one_mul]
      · rw [ZMod.natCast_zmod_val]
        exact hz.symm

/-- The local dimension is one at primes dividing `x` and two otherwise. -/
theorem smoothingTransitionRootCount_prime
    {x p : ℕ} {q : ℕ × ℕ} (hp : p.Prime)
    (hpb : ¬p ∣ q.1 * q.2) :
    smoothingTransitionRootCount x q p =
      if p ∣ x then 1 else 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpb₁ : ¬p ∣ q.1 := fun h =>
    hpb (dvd_mul_of_dvd_left h q.2)
  have hpb₂ : ¬p ∣ q.2 := fun h =>
    hpb (dvd_mul_of_dvd_right h q.1)
  have hbZ :
      (q.1 : ZMod p) * (q.2 : ZMod p) ≠ 0 := by
    exact mul_ne_zero
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₁)
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₂)
  have himage :=
    smoothingTransitionRootResidues_image_prime
      (x := x) (q := q) hp hpb
  have hinj : Set.InjOn
      (fun r : ℕ => (r : ZMod p))
      (smoothingTransitionRootResidues x q p : Set ℕ) := by
    intro r hr s hs hrs
    have hrlt : r < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val hrs
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  calc
    smoothingTransitionRootCount x q p =
        ((smoothingTransitionRootResidues x q p).image
          (fun r : ℕ => (r : ZMod p))).card := by
      unfold smoothingTransitionRootCount
      exact (Finset.card_image_of_injOn hinj).symm
    _ = ({0, ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
          (x : ZMod p)} : Finset (ZMod p)).card := by
      rw [himage]
    _ = if p ∣ x then 1 else 2 := by
      by_cases hx : p ∣ x
      · have hxZ : (x : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff x p).mpr hx
        simp [hx, hxZ]
      · have hxZ : (x : ZMod p) ≠ 0 :=
          (ZMod.natCast_eq_zero_iff x p).not.mpr hx
        have hc :
            ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
                (x : ZMod p) ≠ 0 :=
          mul_ne_zero (inv_ne_zero hbZ) hxZ
        rw [if_neg hx]
        have hzero :
            (0 : ZMod p) ∉
              ({((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
                (x : ZMod p)} : Finset (ZMod p)) := by
          simpa only [Finset.mem_singleton] using hc.symm
        rw [Finset.card_insert_of_notMem hzero]
        simp

/-- Every sieving prime is smaller than both primes in an admissible Chen
pair, hence it does not divide their product. -/
theorem transitionSievePrime_not_dvd_pair
    {x p : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    ¬p ∣ q.1 * q.2 := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with
    ⟨hp₁, hp₂, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
  have hxR : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 100) <
        (x : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_lt_rpow_of_exponent_lt hxR (by norm_num)
  have hpq₁R : (p : ℝ) < (q.1 : ℝ) :=
    (prime_le_transitionThreshold_of_dvd hp hpdvd).trans_lt
      (hpow.trans hp₁lo)
  have hpq₁ : p < q.1 := by exact_mod_cast hpq₁R
  have hq₁q₂R : (q.1 : ℝ) < (q.2 : ℝ) :=
    hp₁hi.trans_lt hp₂lo
  have hpq₂ : p < q.2 := by
    exact_mod_cast hpq₁R.trans hq₁q₂R
  intro hpdiv
  rcases hp.dvd_mul.mp hpdiv with hpdiv | hpdiv
  · have heq : p = q.1 :=
      (Nat.prime_dvd_prime_iff_eq hp hp₁).mp hpdiv
    omega
  · have heq : p = q.2 :=
      (Nat.prime_dvd_prime_iff_eq hp hp₂).mp hpdiv
    omega

theorem pairProduct_mul_le_of_mem_transitionInterval
    {x n : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x)
    (hn : n ∈ smoothingTransitionInterval x q) :
    q.1 * q.2 * n ≤ x := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  have hp₁pos : (0 : ℝ) < q.1 := by
    exact_mod_cast hq'.2.1.pos
  have hp₂pos : (0 : ℝ) < q.2 := by
    exact_mod_cast hq'.2.2.1.pos
  have hnSmoothed := (Finset.mem_filter.mp hn).1
  have hnle :
      (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    (Finset.mem_filter.mp hnSmoothed).2
  have hprod :
      ((q.1 : ℝ) * q.2) * n ≤ (x : ℝ) :=
    by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀ (mul_pos hp₁pos hp₂pos)).mp hnle
  exact_mod_cast hprod

/-- Divisibility of an actual transition value forces its residue to be
one of the polynomial roots modulo the divisor. -/
theorem mod_mem_smoothingTransitionRootResidues
    {x n d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hn : n ∈ smoothingTransitionInterval x q)
    (hdiv : d ∣ smoothingTransitionArgument x q n) :
    n % d ∈ smoothingTransitionRootResidues x q d := by
  have hprod :
      q.1 * q.2 * n ≤ x :=
    pairProduct_mul_le_of_mem_transitionInterval hq hn
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (Nat.mod_lt n hd)
  · rw [ZMod.natCast_mod]
    have hzero :
        (smoothingTransitionArgument x q n : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff
        (smoothingTransitionArgument x q n) d).mpr hdiv
    unfold smoothingTransitionArgument at hzero
    rw [Nat.cast_mul, Nat.cast_sub hprod,
      Nat.cast_mul, Nat.cast_mul] at hzero
    simpa only [Nat.cast_mul, mul_assoc] using hzero

theorem dvd_transitionArgument_iff_mod_mem_roots
    {x n d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hn : n ∈ smoothingTransitionInterval x q) :
    d ∣ smoothingTransitionArgument x q n ↔
      n % d ∈ smoothingTransitionRootResidues x q d := by
  constructor
  · exact mod_mem_smoothingTransitionRootResidues hq hd hn
  · intro hroot
    have hprod :
        q.1 * q.2 * n ≤ x :=
      pairProduct_mul_le_of_mem_transitionInterval hq hn
    have hrootData := (Finset.mem_filter.mp hroot).2
    rw [ZMod.natCast_mod] at hrootData
    have hzero :
        (smoothingTransitionArgument x q n : ZMod d) = 0 := by
      unfold smoothingTransitionArgument
      rw [Nat.cast_mul, Nat.cast_sub hprod,
        Nat.cast_mul, Nat.cast_mul]
      simpa only [Nat.cast_mul, mul_assoc] using hrootData
    exact (ZMod.natCast_eq_zero_iff
      (smoothingTransitionArgument x q n) d).mp hzero

/-! ### Counting divisibility classes in a short integer interval -/

/-- If every solution modulo `d` lands in a prescribed finite root set,
then the number of solutions in `(L,U]` is at most the number of roots
times the number of possible quotients. -/
theorem card_filter_dvd_le_rootCard_mul_intervalQuotients
    {S roots : Finset ℕ} {F : ℕ → ℕ}
    {d L U : ℕ} (hd : 0 < d) (hLU : L ≤ U)
    (hbounds : ∀ n ∈ S, L < n ∧ n ≤ U)
    (hroot : ∀ n ∈ S, d ∣ F n → n % d ∈ roots) :
    ((S.filter fun n => d ∣ F n).card : ℕ) ≤
      roots.card * ((U - L) / d + 2) := by
  let A := S.filter fun n => d ∣ F n
  let enc : ℕ → ℕ × ℕ := fun n => (n % d, n / d)
  let box : Finset (ℕ × ℕ) :=
    roots ×ˢ Finset.Icc (L / d) (U / d)
  have hencinj : Function.Injective enc := by
    intro n m h
    have hmod : n % d = m % d := congrArg Prod.fst h
    have hdiv : n / d = m / d := congrArg Prod.snd h
    calc
      n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
      _ = m % d + d * (m / d) := by rw [hmod, hdiv]
      _ = m := Nat.mod_add_div m d
  have himage : A.image enc ⊆ box := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnA, rfl⟩
    have hnS := (Finset.mem_filter.mp hnA).1
    have hndiv := (Finset.mem_filter.mp hnA).2
    have hnBounds := hbounds n hnS
    apply Finset.mem_product.mpr
    constructor
    · exact hroot n hnS hndiv
    · apply Finset.mem_Icc.mpr
      exact ⟨Nat.div_le_div_right hnBounds.1.le,
        Nat.div_le_div_right hnBounds.2⟩
  have hquot :
      U / d + 1 - L / d ≤ (U - L) / d + 2 := by
    have hU : U = L + (U - L) := by omega
    have hadd :
        (L + (U - L)) / d ≤
          L / d + (U - L) / d + 1 := by
      rw [Nat.add_div hd]
      split <;> omega
    have hadd' :
        U / d ≤ L / d + (U - L) / d + 1 := by
      calc
        U / d = (L + (U - L)) / d :=
          congrArg (fun t : ℕ => t / d) hU
        _ ≤ L / d + (U - L) / d + 1 := hadd
    apply tsub_le_iff_left.mpr
    omega
  calc
    A.card = (A.image enc).card :=
      (Finset.card_image_of_injective A hencinj).symm
    _ ≤ box.card := Finset.card_le_card himage
    _ = roots.card * (U / d + 1 - L / d) := by
      simp only [box, Finset.card_product, Nat.card_Icc]
    _ ≤ roots.card * ((U - L) / d + 2) :=
      Nat.mul_le_mul_left roots.card hquot

/-- A single residue class occurs in `(L,U]` within one unit (we retain a
two-unit symmetric bound) of the quotient `(U-L)/d`. -/
theorem Ioc_modFiber_card_div_bounds
    {L U d r : ℕ} (hd : 0 < d) (hLU : L ≤ U)
    (hr : r < d) :
    let N :=
      ((Finset.Ioc L U).filter fun n => n % d = r).card
    let Q := (U - L) / d
    Q ≤ N + 1 ∧ N ≤ Q + 2 := by
  let FU :=
    (Finset.range (U + 1)).filter fun n => n % d = r
  let FL :=
    (Finset.range (L + 1)).filter fun n => n % d = r
  have hFLFU : FL ⊆ FU := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hn'.1).trans_le (by omega)), hn'.2⟩
  have hinterval :
      (Finset.Ioc L U).filter (fun n => n % d = r) =
        FU \ FL := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, FU, FL, Finset.mem_range]
    omega
  have hFU :
      FU.card = (U + 1) / d +
        if r % d < (U + 1) % d then 1 else 0 := by
    simpa only [FU] using
      (show ((Finset.range (U + 1)).filter fun n =>
          n % d = r).card =
          (U + 1) / d +
            if r % d < (U + 1) % d then 1 else 0 by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hr,
          Nat.count_eq_card_filter_range] using
            Nat.count_modEq_card (U + 1) hd r)
  have hFL :
      FL.card = (L + 1) / d +
        if r % d < (L + 1) % d then 1 else 0 := by
    simpa only [FL] using
      (show ((Finset.range (L + 1)).filter fun n =>
          n % d = r).card =
          (L + 1) / d +
            if r % d < (L + 1) % d then 1 else 0 by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hr,
          Nat.count_eq_card_filter_range] using
            Nat.count_modEq_card (L + 1) hd r)
  have hcard :
      ((Finset.Ioc L U).filter fun n => n % d = r).card =
        FU.card - FL.card := by
    rw [hinterval, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hFLFU]
  have hcardle : FL.card ≤ FU.card :=
    Finset.card_le_card hFLFU
  have hNadd :
      ((Finset.Ioc L U).filter fun n => n % d = r).card +
          FL.card = FU.card := by
    rw [hcard, Nat.sub_add_cancel hcardle]
  have hsum : U + 1 = (L + 1) + (U - L) := by omega
  have hqlo :
      (L + 1) / d + (U - L) / d ≤ (U + 1) / d := by
    rw [hsum]
    exact Nat.div_add_div_le_add_div
  have hqhi :
      (U + 1) / d ≤
        (L + 1) / d + (U - L) / d + 1 := by
    rw [hsum, Nat.add_div hd]
    split <;> omega
  dsimp only
  rw [hFU, hFL] at hNadd
  split_ifs at hNadd <;> omega

/-! ### The actual smoothing transition as a short integer interval -/

noncomputable def smoothingTransitionLower
    (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  ⌊((x : ℝ) / ((q.1 : ℝ) * q.2)) /
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))⌋₊

noncomputable def smoothingTransitionUpper
    (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  ⌊(x : ℝ) / ((q.1 : ℝ) * q.2)⌋₊

noncomputable def positiveSmoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothingTransitionInterval x q).erase 0

theorem mem_positiveSmoothingTransitionInterval_bounds
    {x n : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x)
    (hn : n ∈ positiveSmoothingTransitionInterval x q) :
    smoothingTransitionLower x q < n ∧
      n ≤ smoothingTransitionUpper x q := by
  have hnErase := Finset.mem_erase.mp hn
  have hn0 : n ≠ 0 := hnErase.1
  have hnTransition := hnErase.2
  have hnData := Finset.mem_filter.mp hnTransition
  have hnSmoothed := hnData.1
  have hnle :
      (n : ℝ) ≤
        (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    (Finset.mem_filter.mp hnSmoothed).2
  have hnposR : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  have hp₁pos : (0 : ℝ) < q.1 := by
    exact_mod_cast hq'.2.1.pos
  have hp₂pos : (0 : ℝ) < q.2 := by
    exact_mod_cast hq'.2.2.1.pos
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let E : ℝ :=
    Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))
  have hEpos : 0 < E := by
    dsimp only [E]
    positivity
  have hboundary : Y / n < E := by
    dsimp only [Y, E]
    simpa only [div_div, mul_assoc] using hnData.2
  have hYlt : Y < E * n :=
    (div_lt_iff₀ hnposR).mp hboundary
  have hlowerR : Y / E < n :=
    (div_lt_iff₀ hEpos).mpr (by
      simpa only [mul_comm] using hYlt)
  constructor
  · have hfloor :
        (smoothingTransitionLower x q : ℝ) ≤ Y / E := by
      unfold smoothingTransitionLower
      dsimp only [Y, E]
      exact Nat.floor_le (by positivity)
    have hltR :
        (smoothingTransitionLower x q : ℝ) < n :=
      hfloor.trans_lt hlowerR
    exact_mod_cast hltR
  · unfold smoothingTransitionUpper
    exact Nat.le_floor hnle

theorem positiveSmoothingTransitionInterval_eq_Ioc
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    positiveSmoothingTransitionInterval x q =
      Finset.Ioc (smoothingTransitionLower x q)
        (smoothingTransitionUpper x q) := by
  ext n
  constructor
  · intro hn
    exact Finset.mem_Ioc.mpr
      (mem_positiveSmoothingTransitionInterval_bounds hq hn)
  · intro hn
    have hnBounds := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    have hp₁pos : (0 : ℝ) < q.1 := by
      exact_mod_cast hq'.2.1.pos
    have hp₂pos : (0 : ℝ) < q.2 := by
      exact_mod_cast hq'.2.2.1.pos
    have hp₁one : (1 : ℝ) ≤ q.1 := by
      exact_mod_cast hq'.2.1.one_le
    have hp₂one : (1 : ℝ) ≤ q.2 := by
      exact_mod_cast hq'.2.2.1.one_le
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    let E : ℝ :=
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))
    have hEpos : 0 < E := by
      dsimp only [E]
      positivity
    have hupperFloor :
        (smoothingTransitionUpper x q : ℝ) ≤ Y := by
      unfold smoothingTransitionUpper
      dsimp only [Y]
      exact Nat.floor_le (by positivity)
    have hnleY : (n : ℝ) ≤ Y := by
      have hnUpperR :
          (n : ℝ) ≤ smoothingTransitionUpper x q := by
        exact_mod_cast hnBounds.2
      exact hnUpperR.trans hupperFloor
    have hYleX : Y ≤ (x : ℝ) := by
      dsimp only [Y]
      have hdenom :
          (1 : ℝ) ≤ (q.1 : ℝ) * q.2 := by
        calc
          (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (q.1 : ℝ) * q.2 :=
            mul_le_mul hp₁one hp₂one (by norm_num) (by norm_num)
      exact div_le_self (by positivity)
        hdenom
    have hnleX : n ≤ x := by
      exact_mod_cast hnleY.trans hYleX
    have hlowerCast :
        Y / E <
          (smoothingTransitionLower x q : ℝ) + 1 := by
      unfold smoothingTransitionLower
      dsimp only [Y, E]
      exact Nat.lt_floor_add_one _
    have hsucc :
        smoothingTransitionLower x q + 1 ≤ n := by omega
    have hlower : Y / E < (n : ℝ) := by
      exact hlowerCast.trans_le (by exact_mod_cast hsucc)
    have hYlt : Y < E * n :=
      by
        simpa only [mul_comm] using
          (div_lt_iff₀ hEpos).mp hlower
    have hboundary : Y / n < E :=
      (div_lt_iff₀ hnposR).mpr (by
        simpa only [mul_comm] using hYlt)
    apply Finset.mem_erase.mpr
    refine ⟨by omega, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hnleY⟩
    · dsimp only [Y, E] at hboundary
      simpa only [div_div, mul_assoc] using hboundary

theorem smoothingTransitionLower_le_upper
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    smoothingTransitionLower x q ≤
      smoothingTransitionUpper x q := by
  by_cases hS :
      positiveSmoothingTransitionInterval x q = ∅
  · unfold smoothingTransitionLower smoothingTransitionUpper
    apply Nat.floor_mono
    have hEone :
        1 ≤ Real.exp
          (2 * (Real.log x) ^ (-(0.1 : ℝ))) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    exact div_le_self (by positivity) hEone
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hb :=
      mem_positiveSmoothingTransitionInterval_bounds hq hn
    omega

/-- Congruence counting for the positive part of the actual transition
interval, with the exact local root count. -/
theorem positiveTransition_dvd_card_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    (((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) ≤
      smoothingTransitionRootCount x q d *
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q) / d + 2) := by
  unfold smoothingTransitionRootCount
  apply card_filter_dvd_le_rootCard_mul_intervalQuotients
    hd (smoothingTransitionLower_le_upper hq)
  · intro n hn
    exact mem_positiveSmoothingTransitionInterval_bounds hq hn
  · intro n hn hdiv
    apply mod_mem_smoothingTransitionRootResidues hq hd
    · exact (Finset.mem_erase.mp hn).2
    · exact hdiv

/-- Exact decomposition of a transition divisibility count into its
admissible residue classes. -/
theorem positiveTransition_dvd_card_eq_sum_rootFibers
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    (((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) =
      ∑ r ∈ smoothingTransitionRootResidues x q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
  let S := positiveSmoothingTransitionInterval x q
  let roots := smoothingTransitionRootResidues x q d
  have hfiber :=
    Finset.sum_card_fiberwise_eq_card_filter
      S roots (fun n => n % d)
  calc
    ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        n % d ∈ smoothingTransitionRootResidues x q d).card := by
      apply congrArg Finset.card
      ext n
      simp only [Finset.mem_filter]
      constructor
      · intro hn
        exact ⟨hn.1,
          (dvd_transitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mp hn.2⟩
      · intro hn
        exact ⟨hn.1,
          (dvd_transitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mpr hn.2⟩
    _ = ∑ r ∈ smoothingTransitionRootResidues x q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
      simpa only [S, roots] using hfiber.symm

theorem positiveTransition_rootFiber_abs_sub_density_le
    {x d r : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hr : r ∈ smoothingTransitionRootResidues x q d) :
    |(((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card : ℝ) -
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) / d| ≤ 3 := by
  let L := smoothingTransitionLower x q
  let U := smoothingTransitionUpper x q
  let N :=
    ((Finset.Ioc L U).filter fun n => n % d = r).card
  let Q := (U - L) / d
  have hLU : L ≤ U :=
    smoothingTransitionLower_le_upper hq
  have hrlt : r < d :=
    Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hbounds := Ioc_modFiber_card_div_bounds hd hLU hrlt
  have hNQ :
      |(N : ℝ) - (Q : ℝ)| ≤ 2 := by
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

noncomputable def positiveTransitionDivisibilityCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((positiveSmoothingTransitionInterval x q).filter fun n =>
    d ∣ smoothingTransitionArgument x q n).card : ℝ)

noncomputable def positiveTransitionDivisibilityRemainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  positiveTransitionDivisibilityCount x q d -
    (smoothingTransitionRootCount x q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

/-- The short interval has an absolute distribution remainder bounded by
three times the exact number of local roots. -/
theorem abs_positiveTransitionDivisibilityRemainder_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |positiveTransitionDivisibilityRemainder x q d| ≤
      3 * smoothingTransitionRootCount x q d := by
  let roots := smoothingTransitionRootResidues x q d
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hcount :=
    positiveTransition_dvd_card_eq_sum_rootFibers hq hd
  have hcountR :
      positiveTransitionDivisibilityCount x q d =
        ∑ r ∈ roots,
          (((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) := by
    unfold positiveTransitionDivisibilityCount
    exact_mod_cast hcount
  have hmain :
      (smoothingTransitionRootCount x q d : ℝ) * H / d =
        ∑ _r ∈ roots, H / d := by
    unfold smoothingTransitionRootCount
    simp only [roots, Finset.sum_const, nsmul_eq_mul]
    ring
  unfold positiveTransitionDivisibilityRemainder
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
        positiveTransition_rootFiber_abs_sub_density_le
          hq hd hr
    _ = 3 * smoothingTransitionRootCount x q d := by
      unfold smoothingTransitionRootCount
      simp only [roots, Finset.sum_const, nsmul_eq_mul]
      ring

theorem zero_mem_smoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) :
    0 ∈ smoothingTransitionInterval x q := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · simpa only [Nat.cast_zero] using
        div_nonneg
          (show (0 : ℝ) ≤ (x : ℝ) by positivity)
          (show (0 : ℝ) ≤ (q.1 : ℝ) * q.2 by positivity)
  · simpa using
      (Real.exp_pos
        (2 * (Real.log x) ^ (-(0.1 : ℝ))))

theorem transitionDivisibilityCount_eq_positive_add_one
    {x d : ℕ} {q : ℕ × ℕ} :
    (((smoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card + 1 := by
  let A :=
    (smoothingTransitionInterval x q).filter fun n =>
      d ∣ smoothingTransitionArgument x q n
  let B :=
    (positiveSmoothingTransitionInterval x q).filter fun n =>
      d ∣ smoothingTransitionArgument x q n
  have h0A : 0 ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨zero_mem_smoothingTransitionInterval x q,
      by simp [smoothingTransitionArgument]⟩
  have herase : A.erase 0 = B := by
    ext n
    simp only [A, B, positiveSmoothingTransitionInterval,
      Finset.mem_erase, Finset.mem_filter]
    tauto
  calc
    A.card = (A.erase 0).card + 1 :=
      (Finset.card_erase_add_one h0A).symm
    _ = B.card + 1 := by rw [herase]

noncomputable def transitionDivisibilityCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((smoothingTransitionInterval x q).filter fun n =>
    d ∣ smoothingTransitionArgument x q n).card : ℝ)

noncomputable def transitionDivisibilityRemainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  transitionDivisibilityCount x q d -
    (smoothingTransitionRootCount x q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

/-- Adding back the exceptional index `n = 0` costs exactly one in every
modulus, so the full transition remainder is still uniformly bounded. -/
theorem abs_transitionDivisibilityRemainder_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |transitionDivisibilityRemainder x q d| ≤
      3 * smoothingTransitionRootCount x q d + 1 := by
  have hcountNat :=
    transitionDivisibilityCount_eq_positive_add_one
      (x := x) (q := q) (d := d)
  have hcount :
      transitionDivisibilityCount x q d =
        positiveTransitionDivisibilityCount x q d + 1 := by
    unfold transitionDivisibilityCount
      positiveTransitionDivisibilityCount
    exact_mod_cast hcountNat
  have hpositive :=
    abs_positiveTransitionDivisibilityRemainder_le hq hd
  unfold transitionDivisibilityRemainder
  rw [hcount]
  have hrearrange :
      positiveTransitionDivisibilityCount x q d + 1 -
          (smoothingTransitionRootCount x q d : ℝ) *
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) / d =
        positiveTransitionDivisibilityRemainder x q d + 1 := by
    unfold positiveTransitionDivisibilityRemainder
    ring
  rw [hrearrange]
  calc
    |positiveTransitionDivisibilityRemainder x q d + 1| ≤
        |positiveTransitionDivisibilityRemainder x q d| + |(1 : ℝ)| :=
      abs_add_le _ _
    _ ≤ 3 * smoothingTransitionRootCount x q d + 1 := by
      simpa using add_le_add_right hpositive 1

theorem transitionDivisibilityCount_eq_main_add_remainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) :
    transitionDivisibilityCount x q d =
      (smoothingTransitionRootCount x q d : ℝ) *
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) / d +
        transitionDivisibilityRemainder x q d := by
  unfold transitionDivisibilityRemainder
  ring

noncomputable def transitionMainQuadratic
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      w d₁ * w d₂ *
        ((smoothingTransitionRootCount x q (d₁.lcm d₂) : ℝ) /
          (d₁.lcm d₂ : ℝ))

noncomputable def transitionErrorQuadratic
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      |w d₁ * w d₂| *
        (3 * smoothingTransitionRootCount x q (d₁.lcm d₂) + 1)

/-- Selberg's indexed Λ² inequality with the congruence counts split into
their exact main quadratic form and a nonnegative error majorant. -/
theorem smoothingTransitionSifted_card_le_main_add_error
    {x R : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (w : ℕ → ℝ) (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        transitionMainQuadratic x q R w +
      transitionErrorQuadratic x q R w := by
  let D :=
    truncatedSieveDivisors (transitionSieveProduct x) R
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hsieve :=
    smoothingTransitionSifted_card_le_lcmCount
      x q R w hR hw
  calc
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ *
          transitionDivisibilityCount x q (d₁.lcm d₂) := by
      simpa only [D, transitionDivisibilityCount] using hsieve
    _ = H * transitionMainQuadratic x q R w +
        ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂) := by
      simp_rw [transitionDivisibilityCount_eq_main_add_remainder,
        mul_add, Finset.sum_add_distrib]
      unfold transitionMainQuadratic
      simp only [D]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d₁ hd₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d₂ hd₂
      ring
    _ ≤ H * transitionMainQuadratic x q R w +
        transitionErrorQuadratic x q R w := by
      apply add_le_add_right
      unfold transitionErrorQuadratic
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
      have hlcmpos : 0 < d₁.lcm d₂ := by
        exact Nat.lcm_pos hd₁pos hd₂pos
      have hrem :=
        abs_transitionDivisibilityRemainder_le hq hlcmpos
      calc
        w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂) ≤
          |w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂)| := le_abs_self _
        _ = |w d₁ * w d₂| *
            |transitionDivisibilityRemainder x q
              (d₁.lcm d₂)| := abs_mul _ _
        _ ≤ |w d₁ * w d₂| *
            (3 * smoothingTransitionRootCount x q
              (d₁.lcm d₂) + 1) :=
          mul_le_mul_of_nonneg_left hrem (abs_nonneg _)

end Chen
