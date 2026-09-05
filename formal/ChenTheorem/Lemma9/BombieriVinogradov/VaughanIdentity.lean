import ChenTheorem.Lemma9.BombieriVinogradov.Characters

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Classical

namespace Chen.BombieriVinogradov

/-!
# Vaughan's identity

The analytic proof of Bombieri--Vinogradov starts by splitting the exact
convolution identity `μ * Λ * 1 = Λ` at two cutoffs.  This file records that
algebraic step independently of all subsequent norm estimates.
-/

/-- Restrict an arithmetic function to indices at most `U`. -/
def truncateLE {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

@[simp]
theorem truncateLE_apply {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (U n : ℕ) :
    truncateLE f U n = if n ≤ U then f n else 0 :=
  rfl

/-- Complementary restriction to indices strictly larger than `U`. -/
def truncateGT {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  f - truncateLE f U

@[simp]
theorem truncateGT_apply {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U n : ℕ) :
    truncateGT f U n = if U < n then f n else 0 := by
  rw [truncateGT, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, truncateLE_apply]
  by_cases hn : n ≤ U
  · simp [hn, Nat.not_lt_of_ge hn]
  · have hUn : U < n := Nat.lt_of_not_ge hn
    simp [hn, hUn]

theorem truncateLE_add_truncateGT {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U : ℕ) :
    truncateLE f U + truncateGT f U = f := by
  ext n
  by_cases hn : n ≤ U
  · simp [truncateGT, sub_eq_add_neg, hn]
  · simp [truncateGT, sub_eq_add_neg, hn]

/-- Vaughan's exact decomposition in its standard Type-I/Type-II form.

The first term has the short Möbius variable `d ≤ U`; the next two terms
have all nontrivial convolution variables bounded by `U` and `V`; and the
last term, in which both variables exceed their cutoffs, is Type II. -/
theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          ArithmeticFunction.log +
        (truncateLE ArithmeticFunction.vonMangoldt V -
          truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
            truncateLE ArithmeticFunction.vonMangoldt V *
              ArithmeticFunction.zeta) +
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          truncateGT ArithmeticFunction.vonMangoldt V *
            ArithmeticFunction.zeta := by
  let μL : ArithmeticFunction ℝ :=
    truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U
  let μG : ArithmeticFunction ℝ :=
    truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U
  let ΛL : ArithmeticFunction ℝ :=
    truncateLE ArithmeticFunction.vonMangoldt V
  let ΛG : ArithmeticFunction ℝ :=
    truncateGT ArithmeticFunction.vonMangoldt V
  have hμ : μL + μG =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    exact truncateLE_add_truncateGT _ _
  have hΛ : ΛL + ΛG = ArithmeticFunction.vonMangoldt := by
    exact truncateLE_add_truncateGT _ _
  have hlog : (ΛL + ΛG) * ArithmeticFunction.zeta =
      ArithmeticFunction.log := by
    rw [hΛ, ArithmeticFunction.vonMangoldt_mul_zeta]
  have hshort : (μL + μG) * ΛL * ArithmeticFunction.zeta = ΛL := by
    rw [hμ]
    calc
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ΛL *
          ArithmeticFunction.zeta =
          ΛL * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            ArithmeticFunction.zeta) := by ring
      _ = ΛL := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        simp
  change ArithmeticFunction.vonMangoldt =
    μL * ArithmeticFunction.log +
      (ΛL - μL * ΛL * ArithmeticFunction.zeta) +
      μG * ΛG * ArithmeticFunction.zeta
  calc
    ArithmeticFunction.vonMangoldt =
        (μL + μG) * (ΛL + ΛG) * ArithmeticFunction.zeta := by
      rw [hμ, hΛ, mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta,
        ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
    _ = (μL + μG) * ΛL * ArithmeticFunction.zeta +
          μL * ΛG * ArithmeticFunction.zeta +
          μG * ΛG * ArithmeticFunction.zeta := by
      ring
    _ = ΛL + μL * ΛG * ArithmeticFunction.zeta +
          μG * ΛG * ArithmeticFunction.zeta := by rw [hshort]
    _ = μL * ArithmeticFunction.log +
          (ΛL - μL * ΛL * ArithmeticFunction.zeta) +
          μG * ΛG * ArithmeticFunction.zeta := by
      rw [← hlog]
      ring

/-- First Type-I coefficient in Vaughan's decomposition. -/
noncomputable def vaughanTypeIOne (U : ℕ) : ArithmeticFunction ℝ :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    ArithmeticFunction.log

/-- Second Type-I coefficient in Vaughan's decomposition. -/
noncomputable def vaughanTypeITwo (U V : ℕ) : ArithmeticFunction ℝ :=
  truncateLE ArithmeticFunction.vonMangoldt V -
    truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
      truncateLE ArithmeticFunction.vonMangoldt V * ArithmeticFunction.zeta

/-- Type-II coefficient, in which both nontrivial convolution variables are
larger than their respective cutoffs. -/
noncomputable def vaughanTypeII (U V : ℕ) : ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateGT ArithmeticFunction.vonMangoldt V * ArithmeticFunction.zeta

/-- Pointwise Vaughan identity in the named Type-I/Type-II notation. -/
theorem vonMangoldt_eq_vaughanTypes (U V n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      vaughanTypeIOne U n + vaughanTypeITwo U V n +
        vaughanTypeII U V n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughan_identity U V)
  simpa only [vaughanTypeIOne, vaughanTypeITwo, vaughanTypeII,
    ArithmeticFunction.add_apply, add_assoc] using h

noncomputable def vaughanTypeIOneSum {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeIOne U n : ℂ) * χ n

noncomputable def vaughanTypeITwoSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeITwo U V n : ℂ) * χ n

noncomputable def vaughanTypeIISum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeII U V n : ℂ) * χ n

/-- Vaughan's identity after twisting and summing up to `x`. -/
theorem twistedPsi_eq_vaughanTypes
    {q : ℕ} (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedPsi x χ =
      vaughanTypeIOneSum x U χ + vaughanTypeITwoSum x U V χ +
        vaughanTypeIISum x U V χ := by
  rw [vaughanTypeIOneSum, vaughanTypeITwoSum, vaughanTypeIISum]
  rw [twistedPsi]
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) =
      ∑ n ∈ Finset.Icc 1 x,
        (((vaughanTypeIOne U n : ℝ) : ℂ) +
          ((vaughanTypeITwo U V n : ℝ) : ℂ) +
          ((vaughanTypeII U V n : ℝ) : ℂ)) * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vonMangoldt_eq_vaughanTypes U V n]
      push_cast
      rfl
    _ = (∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeIOne U n : ℂ) * χ n) +
        (∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeITwo U V n : ℂ) * χ n) +
        ∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeII U V n : ℂ) * χ n := by
      simp_rw [add_mul, Finset.sum_add_distrib]

end Chen.BombieriVinogradov
