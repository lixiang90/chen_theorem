import ChenTheorem.Main.ShiftedDefs
import ChenTheorem.Lemma3.FourthMoment

open scoped Classical

namespace Chen

/-!
# Shifted analogues of Lemmas 1--4

The first four lemmas of Chen's argument contain no occurrence of the target
residue.  They therefore apply verbatim when the residue `x` of Theorem 1 is
replaced by the fixed shift `h` of Theorem 2.  The propositions below make
that reuse explicit, so the shifted proof has a nine-lemma dependency chain
rather than beginning at an opaque aggregate estimate.
-/

def ShiftedLemma1 : Prop :=
  (∀ {x y : ℝ}, 1 < x → 0 ≤ y → y ≤ 1 → chenPhi x y = 0) ∧
  (∀ (x : ℝ), 1 < x → ∀ {y : ℝ}, 0 ≤ y → 0 ≤ chenPhi x y) ∧
  (∀ (x : ℝ), 1 < x → ∀ {y : ℝ}, 0 ≤ y → chenPhi x y ≤ 1) ∧
  (∀ (x : ℝ), 1 < x → MonotoneOn (chenPhi x) (Set.Ici 0)) ∧
  (∀ {x y : ℝ}, 1 < x → (10 : ℝ) ^ 4 ≤ Real.log x →
    Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ))) ≤ y →
      1 - x ^ (-(0.1 : ℝ)) ≤ chenPhi x y)

theorem shifted_lemma1 : ShiftedLemma1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun hx hy0 hy1 => chenPhi_eq_zero hx hy0 hy1
  · exact fun x hx y hy => chenPhi_nonneg x hx hy
  · exact fun x hx y hy => chenPhi_le_one x hx hy
  · exact chenPhi_monotoneOn
  · exact fun hx1 hx hy => chenPhi_ge hx1 hx hy

def ShiftedLemma2 : Prop :=
  (∀ (X M N : ℕ) (a : ℕ → ℝ),
    ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (Nat.totient q : ℝ) *
        primSum q (fun χ =>
          ‖∑ n ∈ Finset.Ioc M (M + N), (a n : ℂ) * χ n‖ ^ 2) ≤
      ((X : ℝ) ^ 2 + Real.pi * N) *
        ∑ n ∈ Finset.Ioc M (M + N), (a n) ^ 2) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ (D Q M N : ℕ) (a : ℕ → ℝ),
    1 ≤ D → D ≤ Q →
      ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
          primSum q (fun χ =>
            ‖∑ n ∈ Finset.Ioc M (M + N), (a n : ℂ) * χ n‖ ^ 2) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), (a n) ^ 2)

theorem shifted_lemma2 : ShiftedLemma2 :=
  ⟨large_sieve, large_sieve_dyadic⟩

/-- The corrected height-logarithmic form is the form of Lemma 3 actually
consumed by both the original and fixed-shift arguments. -/
def ShiftedLemma3 : Prop := Lemma3FourthMomentWithHeightLog

theorem shifted_lemma3 : ShiftedLemma3 :=
  lFunction_fourth_moment_with_height_log

def ShiftedLemma4 : Prop :=
  ∀ (k : ℕ), Squarefree k → Odd k → ∀ (m : ℕ), m ≠ 1 →
    ‖∑' χ : DirichletCharacter ℂ k,
        if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) k : ℝ)

theorem shifted_lemma4 : ShiftedLemma4 := by
  intro k hk hodd m hm
  exact primitive_char_sum_bound k hk hodd m hm

end Chen
