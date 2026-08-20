/-
The Fourier--Gauss input for the Pólya--Vinogradov estimate used in
equation (14).  We first establish the exact absolute value of the Gauss
sum of a primitive Dirichlet character for an arbitrary (not necessarily
prime) modulus.  The proof uses finite Fourier inversion on `ZMod q`, so it
also covers the composite moduli occurring in Chen's argument.
-/
import ChenTheorem.Lemma6.RemainderConnection
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.AbelSummation

open scoped Classical
open Finset AddChar ZMod

namespace Chen

/-- Fourier inversion gives the standard product formula for the Gauss
sums of a primitive character and its inverse. -/
theorem primitive_gaussSum_inv_mul_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum χ ZMod.stdAddChar =
      (q : ℂ) * χ (-1 : ZMod q) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv] using hχ
  have hF : ZMod.dft (χ : ZMod q → ℂ) =
      fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hFinv (k : ZMod q) :
      ZMod.dft (fun x : ZMod q => χ⁻¹ x) k =
        χ (-k) * gaussSum χ⁻¹ ZMod.stdAddChar := by
    simpa only [inv_inv] using
      hχinv.fourierTransform_eq_inv_mul_gaussSum k
  have hdft2 := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hdft2
  change ZMod.dft (fun x : ZMod q => χ⁻¹ x) (-1) *
      gaussSum χ ZMod.stdAddChar = (q : ℂ) • χ (-1) at hdft2
  rw [hFinv] at hdft2
  simpa only [neg_one_mul, neg_neg, map_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, mul_comm] using hdft2

/-- Complex conjugation relates the Gauss sum to that of the inverse
character, with the usual `χ(-1)` factor. -/
theorem star_primitive_gaussSum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    star (gaussSum χ ZMod.stdAddChar) =
      χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  rw [star_gaussSum_eq, AddChar.inv_mulShift]
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar
    (-1 : (ZMod q)ˣ)
  simpa only [inv_inv, Units.val_neg, Units.val_one, neg_one_mul] using h

/-- The squared absolute value of the Gauss sum of a primitive Dirichlet
character modulo `q` is exactly `q`. -/
theorem normSq_primitive_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = q := by
  rw [← Complex.ofReal_inj, Complex.normSq_eq_conj_mul_self]
  change star (gaussSum χ ZMod.stdAddChar) *
      gaussSum χ ZMod.stdAddChar = (q : ℂ)
  rw [star_primitive_gaussSum χ, mul_assoc,
    primitive_gaussSum_inv_mul_gaussSum hχ]
  have hneg : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
    rw [← map_mul]
    norm_num
  calc
    χ (-1 : ZMod q) * ((q : ℂ) * χ (-1 : ZMod q)) =
        (q : ℂ) * (χ (-1 : ZMod q) * χ (-1 : ZMod q)) := by ring
    _ = (q : ℂ) := by rw [hneg, mul_one]

/-- Exact square-root size of a primitive Dirichlet-character Gauss sum. -/
theorem norm_primitive_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [Complex.norm_def, normSq_primitive_gaussSum hχ]

/-- Fourier inversion for a primitive Dirichlet character, written in the
normalization used in the Pólya--Vinogradov argument. -/
theorem primitive_character_fourier_expansion
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ * ∑ k : ZMod q,
      ZMod.stdAddChar (k * n) *
        (χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply
    (χ : ZMod q → ℂ)) n
  rw [ZMod.invDFT_apply] at hinv
  rw [← hinv]
  congr 2 with k
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
  rfl

/-- A primitive character of modulus at least two has mean zero over one
complete residue system. -/
theorem primitive_character_sum_one_period
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    ∑ n ∈ Finset.range q, χ n = 0 := by
  have hne : χ ≠ 1 := by
    intro heq
    rw [heq, DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_one] at hχ
    omega
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin q, χ (i : ℕ) = ∑ a : ZMod q, χ a := by
      apply Fintype.sum_equiv (ZMod.finEquiv q)
      intro i
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q =>
          exact congrArg χ (@ZMod.natCast_zmod_val (q + 1)
            inferInstance ((i : Fin (q + 1)) : ZMod (q + 1)))
    _ = 0 := χ.sum_eq_zero_of_ne_one hne

/-- Dirichlet characters are periodic with their modulus. -/
theorem dirichletCharacter_nat_add_modulus
    (q : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (q + n) = χ n := by
  congr
  simp

/-- Every character prefix sum reduces to the final incomplete residue
block.  Complete blocks vanish for primitive characters of modulus `q ≥ 2`. -/
theorem primitive_character_prefix_sum_eq_mod
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ∑ n ∈ range N, χ n = ∑ n ∈ range (N % q), χ n := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < q
      · rw [Nat.mod_eq_of_lt hN]
      · have hqN : q ≤ N := le_of_not_gt hN
        have hqpos : 0 < q := by omega
        have hsub : N - q < N := Nat.sub_lt (by omega) hqpos
        have hsplit : N = q + (N - q) := by omega
        rw [hsplit, Finset.sum_range_add]
        rw [primitive_character_sum_one_period hχ hq, zero_add]
        have htail : ∑ x ∈ range (N - q), χ (q + x) =
            ∑ x ∈ range (N - q), χ x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact dirichletCharacter_nat_add_modulus q χ x
        simp_rw [Nat.cast_add]
        rw [htail, ih (N - q) hsub]
        congr 2
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]

/-- A finite additive-character prefix sum, the elementary geometric
progression occurring after Fourier inversion. -/
noncomputable def additiveCharacterPrefix
    {q : ℕ} [NeZero q] (k : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ZMod.stdAddChar (k * (n : ZMod q))

/-- Fourier expansion of a finite character prefix. -/
theorem primitive_character_prefix_fourier
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ∑ n ∈ range N, χ n =
      ∑ k : ZMod q, (q : ℂ)⁻¹ * χ⁻¹ (-k) *
        gaussSum χ ZMod.stdAddChar * additiveCharacterPrefix k N := by
  calc
    ∑ n ∈ range N, χ n =
        ∑ n ∈ range N, ∑ k : ZMod q,
          (q : ℂ)⁻¹ * χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar *
            ZMod.stdAddChar (k * (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primitive_character_fourier_expansion hχ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      let a : ℂ := (q : ℂ)⁻¹
      let b : ℂ := ZMod.stdAddChar (k * (n : ZMod q))
      let c : ℂ := χ⁻¹ (-k)
      let d : ℂ := gaussSum χ ZMod.stdAddChar
      change a * (b * (c * d)) = a * c * d * b
      ac_rfl
    _ = _ := (Finset.sum_comm).trans (by
      apply Finset.sum_congr rfl
      intro k hk
      rw [additiveCharacterPrefix, Finset.mul_sum])

end Chen
