import ChenTheorem.LargeSieve.Character
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Bombieri--Vinogradov: definitions

This file fixes the exact level-of-distribution statement used by the
Richert sieve.  Later files reduce it to a mean-value estimate for primitive
Dirichlet characters and prove that estimate from Vaughan's identity and the
character large sieve already available in `ChenTheorem.LargeSieve`.
-/

/-- Chebyshev's `ψ` function restricted to the residue class `a mod q`. -/
noncomputable def progressionPsi (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n ≡ a [MOD q] then ArithmeticFunction.vonMangoldt n else 0

/-- The error in the expected main term `x / φ(q)` for one reduced residue
class. -/
noncomputable def progressionError (x q a : ℕ) : ℝ :=
  |progressionPsi x q a - (x : ℝ) / (Nat.totient q : ℝ)|

/-- The error attached to `a` when `a` is a reduced residue, and zero for the
other representatives in `0, ..., q-1`. -/
noncomputable def reducedProgressionError (x q a : ℕ) : ℝ :=
  if a.Coprime q then progressionError x q a else 0

/-- Maximum progression error over reduced residue classes modulo `q`.
The `q = 0` branch makes the definition total; Bombieri--Vinogradov only sums
over positive moduli. -/
noncomputable def maxProgressionError (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0
  else
    (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
      (reducedProgressionError x q)

/-- The von-Mangoldt sum twisted by a Dirichlet character. -/
noncomputable def twistedPsi {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n

/-- Classical Bombieri--Vinogradov at level `1/2`, in an eventual form.

For every logarithmic saving `A`, one may choose a logarithmic loss `B` in
the level `Q ≤ √x / (log x)^B`, uniformly for every such `Q`. -/
def Statement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ Q : ℕ,
          (Q : ℝ) ≤
              Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B →
            ∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q ≤
              C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

theorem progressionPsi_nonneg (x q a : ℕ) :
    0 ≤ progressionPsi x q a := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem progressionError_nonneg (x q a : ℕ) :
    0 ≤ progressionError x q a :=
  abs_nonneg _

theorem reducedProgressionError_nonneg (x q a : ℕ) :
    0 ≤ reducedProgressionError x q a := by
  rw [reducedProgressionError]
  split_ifs
  · exact progressionError_nonneg x q a
  · exact le_rfl

theorem maxProgressionError_nonneg (x q : ℕ) :
    0 ≤ maxProgressionError x q := by
  by_cases hq : q = 0
  · simp [maxProgressionError, hq]
  · rw [maxProgressionError, dif_neg hq]
    calc
      0 ≤ reducedProgressionError x q 0 :=
        reducedProgressionError_nonneg x q 0
      _ ≤ (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
          (reducedProgressionError x q) :=
        Finset.le_sup' _ (Finset.mem_range.2 (Nat.pos_of_ne_zero hq))

theorem progressionError_le_maxProgressionError
    {x q a : ℕ} (hq : q ≠ 0) (ha : a < q) (hac : a.Coprime q) :
    progressionError x q a ≤ maxProgressionError x q := by
  rw [maxProgressionError, dif_neg hq]
  calc
    progressionError x q a = reducedProgressionError x q a := by
      simp only [reducedProgressionError, if_pos hac]
    _ ≤ (Finset.range q).sup' (Finset.nonempty_range_iff.2 hq)
        (reducedProgressionError x q) :=
      Finset.le_sup' _ (Finset.mem_range.2 ha)

theorem sum_maxProgressionError_nonneg (x Q : ℕ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q := by
  exact Finset.sum_nonneg fun q _ => maxProgressionError_nonneg x q

end Chen.BombieriVinogradov
