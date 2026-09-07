import Submission.ChenTheorem.Lemma9.LinearSieve.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List

set_option autoImplicit true

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-!
Constructive beta=2 (cubic cutoff) Rosser sieve.

The recursion is Buchstab's identity with alternating bounds. A lower
branch is discarded when its remaining level is at most the square of
its current prime bound. After selecting a prime p this becomes the
usual cubic condition p^3 < D. The lower bound is deliberately zero
when D <= z^2, where the linear sieve has no positive main term.

Reference: T. Tao, "254A, Notes 4: Some sieve theory", Proposition 14 and
the beta-sieve construction, 2015-01-21. The proofs below are local Lean
proofs; the reference is not a mathematical dependency.
-/

/-- The finite local-density product, with an exclusive prime cutoff. -/
noncomputable def sieveProduct (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∏ p ∈ range z, (1 - if p ∈ P then w p else 0)

/-- Exact finite Buchstab identity for an arbitrary local-density function. -/
theorem sieveProduct_buchstab (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ) :
    sieveProduct P w z = 1 - ∑ p : Fin z,
      if (p : ℕ) ∈ P then w p * sieveProduct P w p else 0 := by
  unfold sieveProduct
  rw [prod_one_sub_ordered, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro p hp
  have hpz := p.isLt
  have hfilter : (range z).filter (· < (p : ℕ)) = range (p : ℕ) := by
    ext q
    simp only [mem_filter, mem_range]
    omega
  rw [hfilter]
  split_ifs <;> simp

theorem sieveProduct_nonneg (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ)
    (hw : ∀ p ∈ P, w p ≤ 1) : 0 ≤ sieveProduct P w z := by
  apply prod_nonneg
  intro p _
  split_ifs with hp
  · exact sub_nonneg.mpr (hw p hp)
  · norm_num

/-- The actual finite recursive upper/lower sieve polynomials. -/
noncomputable def rosserEval (P : Finset ℕ) (w : ℕ → ℝ)
    (z : ℕ) (upper : Bool) (D : ℝ) : ℝ :=
  if upper = false ∧ D ≤ (z : ℝ) ^ 2 then 0
  else 1 - ∑ p : Fin z, if (p : ℕ) ∈ P then
    w p * rosserEval P w p (!upper) (D / p) else 0
termination_by z

theorem rosserEval_upper (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ) (D : ℝ) :
    rosserEval P w z true D = 1 - ∑ p : Fin z,
      if (p : ℕ) ∈ P then w p * rosserEval P w p false (D / p) else 0 := by
  rw [rosserEval]
  simp

theorem rosserEval_lower (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ) (D : ℝ) :
    rosserEval P w z false D = if D ≤ (z : ℝ) ^ 2 then 0 else
      1 - ∑ p : Fin z,
        if (p : ℕ) ∈ P then w p * rosserEval P w p true (D / p) else 0 := by
  rw [rosserEval]
  simp

/-- The recursive coefficients give genuine lower and upper bounds.
No existence theorem for sieve coefficients is assumed here. -/
theorem rosserEval_bounds (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (z : ℕ) (D : ℝ) :
    rosserEval P w z false D ≤ sieveProduct P w z ∧
      sieveProduct P w z ≤ rosserEval P w z true D := by
  induction z using Nat.strong_induction_on generalizing D with
  | h z ih =>
    constructor
    · rw [rosserEval_lower]
      split_ifs with hstop
      · exact sieveProduct_nonneg P w z (fun p hp => (hw p hp).2)
      · rw [sieveProduct_buchstab]
        apply sub_le_sub_left
        apply sum_le_sum
        intro p _
        split_ifs with hp
        · exact mul_le_mul_of_nonneg_left (ih p p.isLt (D / p)).2 (hw p hp).1
        · exact le_rfl
    · rw [rosserEval_upper, sieveProduct_buchstab]
      apply sub_le_sub_left
      apply sum_le_sum
      intro p _
      split_ifs with hp
      · exact mul_le_mul_of_nonneg_left (ih p p.isLt (D / p)).1 (hw p hp).1
      · exact le_rfl

/-- The explicit finite list of surviving decreasing prime strings.
Their coefficients are the signs `(-1)^length`; no weights are chosen
nonconstructively. -/
noncomputable def rosserTerms (P : Finset ℕ) (z : ℕ)
    (upper : Bool) (D : ℝ) : List (List ℕ) :=
  if upper = false ∧ D ≤ (z : ℝ) ^ 2 then []
  else [] :: (List.finRange z).flatMap fun (p : Fin z) =>
    if (p : ℕ) ∈ P then
      (rosserTerms P p (!upper) (D / p)).map (fun ps => (p : ℕ) :: ps)
    else []
termination_by z

/-- One signed monomial in the sieve polynomial. -/
noncomputable def rosserTermValue (w : ℕ → ℝ) (ps : List ℕ) : ℝ :=
  (-1 : ℝ) ^ ps.length * (ps.map w).prod

@[simp] theorem rosserTermValue_nil (w : ℕ → ℝ) : rosserTermValue w [] = 1 := by
  simp [rosserTermValue]

@[simp] theorem rosserTermValue_cons (w : ℕ → ℝ) (p : ℕ) (ps : List ℕ) :
    rosserTermValue w (p :: ps) = -w p * rosserTermValue w ps := by
  simp only [rosserTermValue, List.length_cons, List.map_cons, List.prod_cons, pow_succ]
  ring

/-- The finite terms explicitly expand the recursive polynomial. -/
theorem rosserTerms_sum (P : Finset ℕ) (w : ℕ → ℝ)
    (z : ℕ) (upper : Bool) (D : ℝ) :
    ((rosserTerms P z upper D).map (rosserTermValue w)).sum =
      rosserEval P w z upper D := by
  induction z using Nat.strong_induction_on generalizing upper D with
  | h z ih =>
    rw [rosserTerms, rosserEval]
    split_ifs with hstop
    · simp
    · simp only [List.map_cons, List.sum_cons, rosserTermValue_nil,
        List.flatMap, List.map_flatten, List.sum_flatten, List.map_map,
        Function.comp_def]
      have hbranch (p : Fin z) :
          ((if (p : ℕ) ∈ P then
            (rosserTerms P p (!upper) (D / p)).map (fun ps => (p : ℕ) :: ps)
            else []).map (rosserTermValue w)).sum =
          -(if (p : ℕ) ∈ P then w p * rosserEval P w p (!upper) (D / p) else 0) := by
        split_ifs with hp
        · simp only [List.map_map, Function.comp_def, rosserTermValue_cons,
            List.sum_map_mul_left, ih p p.isLt]
          ring
        · simp
      simp_rw [hbranch]
      rw [← Fin.sum_univ_def, Finset.sum_neg_distrib]
      ring

/-- Every factor in every term comes from the sifting set and lies below
the current exclusive cutoff. -/
theorem mem_rosserTerms_factors (P : Finset ℕ) (z : ℕ)
    (upper : Bool) (D : ℝ) {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) :
    ∀ p ∈ ps, p ∈ P ∧ p < z := by
  induction z using Nat.strong_induction_on generalizing upper D ps with
  | h z ih =>
    rw [rosserTerms] at hps
    split_ifs at hps with hstop
    · simp at hps
    · rcases List.mem_cons.mp hps with rfl | hps
      · simp
      · rcases List.mem_flatMap.mp hps with ⟨q, _, hq⟩
        split_ifs at hq with hqP
        · rcases List.mem_map.mp hq with ⟨qs, hqs, rfl⟩
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨hqP, q.isLt⟩
          · obtain ⟨hpP, hpq⟩ := ih q q.isLt (!upper) (D / q) hqs p hp
            exact ⟨hpP, hpq.trans q.isLt⟩
        · simp at hq

/-- The strings are strictly decreasing, so no prime is repeated. -/
theorem mem_rosserTerms_pairwise (P : Finset ℕ) (z : ℕ)
    (upper : Bool) (D : ℝ) {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) :
    ps.Pairwise (· > ·) := by
  induction z using Nat.strong_induction_on generalizing upper D ps with
  | h z ih =>
    rw [rosserTerms] at hps
    split_ifs at hps with hstop
    · simp at hps
    · rcases List.mem_cons.mp hps with rfl | hps
      · simp
      · rcases List.mem_flatMap.mp hps with ⟨p, _, hp⟩
        split_ifs at hp with hpP
        · rcases List.mem_map.mp hp with ⟨qs, hqs, rfl⟩
          exact List.pairwise_cons.mpr ⟨
            fun q hq => (mem_rosserTerms_factors P p (!upper) (D / p) hqs q hq).2,
            ih p p.isLt (!upper) (D / p) hqs⟩
        · simp at hp

/-- A nonempty lower expansion certifies that its stopping test passed. -/
theorem rosserTerms_lower_level {P : Finset ℕ} {z : ℕ} {D : ℝ}
    {ps : List ℕ} (hps : ps ∈ rosserTerms P z false D) : (z : ℝ) ^ 2 < D := by
  rw [rosserTerms] at hps
  by_contra h
  simp [not_lt.mp h] at hps

/-- Every monomial is below the requested sieve level. -/
theorem mem_rosserTerms_prod_lt (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (z : ℕ) (upper : Bool) (D : ℝ)
    (hD : 1 < D) {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) :
    (ps.prod : ℝ) < D := by
  induction z using Nat.strong_induction_on generalizing upper D ps with
  | h z ih =>
    rw [rosserTerms] at hps
    split_ifs at hps with hstop
    · simp at hps
    · rcases List.mem_cons.mp hps with rfl | hps
      · simpa using hD
      · rcases List.mem_flatMap.mp hps with ⟨p, _, hp⟩
        split_ifs at hp with hpP
        · rcases List.mem_map.mp hp with ⟨qs, hqs, rfl⟩
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hpP
          have hp0 : (0 : ℝ) < p := by linarith
          have hbudget : 1 < D / p := by
            cases upper
            · have hz : (z : ℝ) ^ 2 < D := by simpa using hstop
              have hpz : (p : ℝ) < z := by exact_mod_cast p.isLt
              apply (lt_div_iff₀ hp0).mpr
              nlinarith
            · have hchild : (p : ℝ) ^ 2 < D / p :=
                rosserTerms_lower_level (by simpa using hqs)
              nlinarith
          have hchild := ih p p.isLt (!upper) (D / p) hbudget hqs
          rw [List.prod_cons, Nat.cast_mul]
          have hmul := mul_lt_mul_of_pos_left hchild hp0
          simpa [mul_div_cancel₀ _ hp0.ne'] using hmul
        · simp at hp

/-- No monomial is generated twice by the recursion. -/
theorem rosserTerms_nodup (P : Finset ℕ) (z : ℕ) (upper : Bool) (D : ℝ) :
    (rosserTerms P z upper D).Nodup := by
  induction z using Nat.strong_induction_on generalizing upper D with
  | h z ih =>
    rw [rosserTerms]
    split_ifs with hstop
    · simp
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hempty
        rcases List.mem_flatMap.mp hempty with ⟨p, _, hp⟩
        split_ifs at hp <;> simp at hp
      · apply List.nodup_flatMap.mpr
        constructor
        · intro p _
          split_ifs
          · exact (ih p p.isLt (!upper) (D / p)).map
              (fun _ _ h => List.cons.inj h |>.2)
          · simp
        · apply (List.nodup_finRange z).imp
          intro p q hpq ps hp hq
          dsimp only at hp hq
          split_ifs at hp hq <;> try simp at hp hq
          rcases hp with ⟨ps', _, hps'⟩
          rcases hq with ⟨qs', _, hqs'⟩
          exact hpq (Fin.ext (List.cons.inj (hps'.trans hqs'.symm)).1)

/-- Unique prime factorization makes the product an injective index for
the surviving strings. -/
theorem rosserTerms_prod_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    {ps qs : List ℕ} (hps : ps ∈ rosserTerms P z upper D)
    (hqs : qs ∈ rosserTerms P z upper D) (heq : ps.prod = qs.prod) : ps = qs := by
  have hp : ∀ p ∈ ps, Nat.Prime p := fun p hp =>
    hP p (mem_rosserTerms_factors P z upper D hps p hp).1
  have hq : ∀ q ∈ qs, Nat.Prime q := fun q hq =>
    hP q (mem_rosserTerms_factors P z upper D hqs q hq).1
  have hperm : ps.Perm qs :=
    (Nat.primeFactorsList_unique heq hp).trans
      (Nat.primeFactorsList_unique rfl hq).symm
  exact List.Perm.eq_of_pairwise'
    ((mem_rosserTerms_pairwise P z upper D hps).imp (fun h => Nat.le_of_lt h))
    ((mem_rosserTerms_pairwise P z upper D hqs).imp (fun h => Nat.le_of_lt h)) hperm

/-- The actual arithmetic sieve coefficient. Its defining witness is
unique when `P` consists of primes. -/
noncomputable def rosserCoefficient (P : Finset ℕ) (z : ℕ)
    (upper : Bool) (D : ℝ) (d : ℕ) : ℝ :=
  if h : ∃ ps ∈ rosserTerms P z upper D, ps.prod = d then
    (-1 : ℝ) ^ (Classical.choose h).length
  else 0

/-- The coefficients have absolute value at most one. -/
theorem abs_rosserCoefficient_le_one (P : Finset ℕ) (z : ℕ)
    (upper : Bool) (D : ℝ) (d : ℕ) :
    |rosserCoefficient P z upper D d| ≤ 1 := by
  unfold rosserCoefficient
  split_ifs <;> simp [abs_pow]

/-- The coefficients vanish outside the level of support. -/
theorem rosserCoefficient_eq_zero_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    (hD : 1 < D) (d : ℕ) (hd : D ≤ d) :
    rosserCoefficient P z upper D d = 0 := by
  unfold rosserCoefficient
  rw [dif_neg]
  rintro ⟨ps, hps, rfl⟩
  exact (mem_rosserTerms_prod_lt P (fun p hp => (hP p hp).two_le)
    z upper D hD hps).not_ge hd

theorem rosserCoefficient_eq_term (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) :
    rosserCoefficient P z upper D ps.prod = (-1 : ℝ) ^ ps.length := by
  have hex : ∃ qs ∈ rosserTerms P z upper D, qs.prod = ps.prod := ⟨ps, hps, rfl⟩
  rw [rosserCoefficient, dif_pos hex]
  have hchoose := Classical.choose_spec hex
  rw [rosserTerms_prod_injective P hP z upper D hchoose.1 hps hchoose.2]

end Chen.LinearSieve
