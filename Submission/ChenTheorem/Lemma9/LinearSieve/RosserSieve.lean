import Submission.ChenTheorem.Lemma9.LinearSieve.RosserWeights

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserTerms_prod_dvd (P : Finset ℕ) (z : ℕ) (upper : Bool) (D : ℝ)
    {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) :
    ps.prod ∣ ∏ p ∈ P, p := by
  have hsort := mem_rosserTerms_pairwise P z upper D hps
  have hnodup : ps.Nodup := hsort.imp (fun h => ne_of_gt h)
  have heq : ∏ p ∈ ps.toFinset, p = ps.prod := by
    simpa using List.prod_toFinset id hnodup
  rw [← heq]
  exact prod_dvd_prod_of_subset _ P id (fun p hp =>
    (mem_rosserTerms_factors P z upper D hps p (List.mem_toFinset.mp hp)).1)

/-- The main sum for an arbitrary multiplicative density is exactly the
explicit Rosser polynomial, not an additional asymptotic input. -/
theorem rosser_main_sum (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (z : ℕ) (upper : Bool) (D : ℝ)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, rosserCoefficient P z upper D d * g d) =
      rosserEval P g z upper D := by
  rw [sum_rosserCoefficient P hP, ← rosserTerms_sum]
  rw [← List.sum_toFinset _ (rosserTerms_nodup P z upper D)]
  apply sum_congr rfl
  intro ps hps
  have hmem := List.mem_toFinset.mp hps
  have hprod0 : (∏ p ∈ P, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)
  rw [if_pos (Nat.mem_divisors.mpr ⟨rosserTerms_prod_dvd P z upper D hmem, hprod0⟩)]
  unfold rosserTermValue
  congr 1
  have hsort := mem_rosserTerms_pairwise P z upper D hmem
  have hn : ps.Nodup := hsort.imp (fun h => ne_of_gt h)
  have heq : ∏ p ∈ ps.toFinset, p = ps.prod := by
    simpa using List.prod_toFinset id hn
  rw [← heq, hg.map_prod_of_prime _ (fun p hp =>
    hP p (mem_rosserTerms_factors P z upper D hmem p (List.mem_toFinset.mp hp)).1)]
  exact List.prod_toFinset g hn

/-- The constructed upper/lower weights applied to a genuine finite
BoundingSieve, with their exact main polynomials and absolute remainders. -/
theorem rosser_sieve_bounds (s : BoundingSieve) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : s.prodPrimes = ∏ p ∈ P, p)
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) :
    s.totalMass * rosserEval P s.nu z false D -
        s.errSum (rosserCoefficient P z false D) ≤ s.siftedSum ∧
      s.siftedSum ≤ s.totalMass * rosserEval P s.nu z true D +
        s.errSum (rosserCoefficient P z true D) := by
  have hmain (upper : Bool) : s.mainSum (rosserCoefficient P z upper D) =
      rosserEval P s.nu z upper D := by
    unfold BoundingSieve.mainSum
    rw [hprod]
    exact rosser_main_sum P hP z upper D s.nu s.nu_mult
  have hlower : IsLowerMoebius s.prodPrimes (rosserCoefficient P z false D) := by
    simpa only [hprod] using rosserCoefficient_isLowerMoebius P hP z hz D
  constructor
  · simpa only [hmain] using
      mainSum_sub_errSum_le_siftedSum (s := s) _ hlower
  · simpa only [hmain] using
      s.siftedSum_le_mainSum_errSum_of_upperMoebius _
        (rosserCoefficient_isUpperMoebius P hP z D)

/-- A finite form ready to receive a distribution estimate: the
coefficients are constructed, and only the actual arithmetic error
majorants and the explicit recursive main polynomials remain. -/
theorem rosser_sieve_bounds_of_remainders (s : BoundingSieve) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : s.prodPrimes = ∏ p ∈ P, p)
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) (E : ℕ → ℝ) (hE : ∀ d, 0 ≤ E d)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, d ≤ Q → |s.rem d| ≤ E d) :
    s.totalMass * rosserEval P s.nu z false D - (∑ d ∈ Icc 1 Q, E d) ≤ s.siftedSum ∧
      s.siftedSum ≤ s.totalMass * rosserEval P s.nu z true D + (∑ d ∈ Icc 1 Q, E d) := by
  have herr (upper : Bool) : s.errSum (rosserCoefficient P z upper D) ≤
      ∑ d ∈ Icc 1 Q, E d := by
    apply errSum_le_sum_of_level _ E Q
    · intro d hd
      apply rosserCoefficient_eq_zero_of_level P hP z upper D hD d
      exact hDQ.trans (by exact_mod_cast hd.le)
    · intro d _
      exact abs_rosserCoefficient_le_one P z upper D d
    · exact hE
    · exact hrem
  obtain ⟨hlower, hupper⟩ := rosser_sieve_bounds s P hP hprod z hz D
  constructor
  · exact (sub_le_sub_left (herr false) _).trans hlower
  · exact hupper.trans (_root_.add_le_add le_rfl (herr true))

/-- A version retaining the actual divisor support in the error sum.
This is needed when several sieved subsequences are summed: keeping the
support can prevent an artificial divisor multiplicity loss. -/
theorem rosser_sieve_bounds_of_divisor_remainders (s : BoundingSieve) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : s.prodPrimes = ∏ p ∈ P, p)
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) (E : ℕ → ℝ)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, d ≤ Q → |s.rem d| ≤ E d) :
    s.totalMass * rosserEval P s.nu z false D -
        (∑ d ∈ s.prodPrimes.divisors with d ≤ Q, E d) ≤ s.siftedSum ∧
      s.siftedSum ≤ s.totalMass * rosserEval P s.nu z true D +
        (∑ d ∈ s.prodPrimes.divisors with d ≤ Q, E d) := by
  have herr (upper : Bool) : s.errSum (rosserCoefficient P z upper D) ≤
      ∑ d ∈ s.prodPrimes.divisors with d ≤ Q, E d := by
    rw [Finset.sum_filter]
    apply sum_le_sum
    intro d hd
    by_cases hdQ : d ≤ Q
    · rw [if_pos hdQ]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_rosserCoefficient_le_one P z upper D d)).trans
        (hrem d hd hdQ)
    · rw [if_neg hdQ]
      have hzero := rosserCoefficient_eq_zero_of_level P hP z upper D hD d
        (hDQ.trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hdQ))))
      rw [hzero, abs_zero, zero_mul]
  obtain ⟨hlower, hupper⟩ := rosser_sieve_bounds s P hP hprod z hz D
  exact ⟨(sub_le_sub_left (herr false) _).trans hlower,
    hupper.trans (_root_.add_le_add le_rfl (herr true))⟩

end Chen.LinearSieve
