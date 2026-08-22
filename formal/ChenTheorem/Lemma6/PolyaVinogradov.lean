/-
The Fourier--Gauss input for the Pólya--Vinogradov estimate used in
equation (14).  We first establish the exact absolute value of the Gauss
sum of a primitive Dirichlet character for an arbitrary (not necessarily
prime) modulus.  The proof uses finite Fourier inversion on `ZMod q`, so it
also covers the composite moduli occurring in Chen's argument.
-/
import ChenTheorem.Lemma6.RemainderConnection
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Harmonic.Bounds
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

/-- The elementary geometric bound for a nontrivial additive-character
prefix. -/
theorem additiveCharacterPrefix_norm_le
    {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ≠ 0) (N : ℕ) :
    ‖additiveCharacterPrefix k N‖ ≤
      2 / ‖ZMod.stdAddChar k - 1‖ := by
  have hchar : ZMod.stdAddChar k ≠ 1 := by
    intro h
    have heq : ZMod.stdAddChar k =
        ZMod.stdAddChar (0 : ZMod q) := by simpa using h
    exact hk (ZMod.injective_stdAddChar heq)
  have hsum : additiveCharacterPrefix k N =
      ∑ n ∈ range N, (ZMod.stdAddChar k) ^ n := by
    unfold additiveCharacterPrefix
    apply Finset.sum_congr rfl
    intro n hn
    rw [show ZMod.stdAddChar (k * (n : ZMod q)) =
      (ZMod.stdAddChar k) ^ n by
        rw [mul_comm]
        have hmul : (n : ZMod q) * k = n • k := by
          simpa using
            (Nat.cast_smul_eq_nsmul (R := ZMod q) n k).symm
        rw [hmul, AddChar.map_nsmul_eq_pow]]
  rw [hsum, geom_sum_eq hchar, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖ZMod.stdAddChar k ^ N - 1‖ ≤
        ‖ZMod.stdAddChar k ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp only [norm_pow, AddChar.norm_apply, one_pow, norm_one]
      norm_num

/-- On the first half of a residue system the distance of the standard
additive character from one is bounded below linearly. -/
theorem stdAddChar_sub_one_norm_lower_bound_nat
    {q d : ℕ} [NeZero q] (hd : d ≤ q / 2) :
    4 * (d : ℝ) / q ≤
      ‖ZMod.stdAddChar (d : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hdq : (d : ℝ) / q ≤ 1 / 2 := by
    rw [div_le_iff₀ hq]
    have hcast : (d : ℝ) * 2 ≤ q := by
      exact_mod_cast
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hd
    nlinarith
  have hangle : |Real.pi * (d : ℝ) / q| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (by positivity)]
    calc
      Real.pi * (d : ℝ) / q = Real.pi * ((d : ℝ) / q) := by ring
      _ ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hdq Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [show (d : ZMod q) = ((d : ℤ) : ZMod q) by norm_cast,
    ZMod.stdAddChar_coe]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (d : ℤ) / (q : ℕ)) =
        Complex.exp (Complex.I *
          ((2 * Real.pi * d / q : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : |Real.pi * (d : ℝ) / q| =
      Real.pi * d / q := abs_of_nonneg (by positivity)
  rw [show (2 * Real.pi * (d : ℝ) / q) / 2 =
      Real.pi * d / q by ring]
  rw [harg] at hsin
  field_simp at hsin ⊢
  nlinarith [Real.pi_pos]

/-- Replacing a frequency by its negative does not change its distance
from one on the unit circle. -/
theorem stdAddChar_neg_sub_one_norm
    {q : ℕ} [NeZero q] (k : ZMod q) :
    ‖ZMod.stdAddChar (-k) - 1‖ =
      ‖ZMod.stdAddChar k - 1‖ := by
  rw [AddChar.map_neg_eq_inv]
  let z := ZMod.stdAddChar k
  have hzNorm : ‖z‖ = 1 := by simp [z]
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzNorm
    norm_num at hzNorm
  calc
    ‖z⁻¹ - 1‖ = ‖z⁻¹ * (1 - z)‖ := by
      congr 1
      field_simp
    _ = ‖z⁻¹‖ * ‖1 - z‖ := norm_mul _ _
    _ = ‖1 - z‖ := by rw [norm_inv, hzNorm, inv_one, one_mul]
    _ = ‖z - 1‖ := norm_sub_rev _ _

/-- The denominator in the geometric estimate is controlled by the
centered representative of the frequency. -/
theorem stdAddChar_sub_one_norm_lower_bound
    {q : ℕ} [NeZero q] (k : ZMod q) :
    4 * (k.valMinAbs.natAbs : ℝ) / q ≤
      ‖ZMod.stdAddChar k - 1‖ := by
  let d := k.valMinAbs.natAbs
  have hd : d ≤ q / 2 := ZMod.natAbs_valMinAbs_le k
  have hbase : 4 * (d : ℝ) / q ≤
      ‖ZMod.stdAddChar (d : ZMod q) - 1‖ :=
    stdAddChar_sub_one_norm_lower_bound_nat hd
  rw [ZMod.natCast_natAbs_valMinAbs] at hbase
  split at hbase
  · simpa only [d] using hbase
  · rw [stdAddChar_neg_sub_one_norm k] at hbase
    simpa only [d] using hbase

/-- The centered geometric-progression estimate used in the
Pólya--Vinogradov argument. -/
theorem additiveCharacterPrefix_norm_le_centered
    {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ≠ 0) (N : ℕ) :
    ‖additiveCharacterPrefix k N‖ ≤
      (q : ℝ) / (2 * k.valMinAbs.natAbs) := by
  let d := k.valMinAbs.natAbs
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by
      rw [Nat.pos_iff_ne_zero]
      intro hd
      have hval : k.valMinAbs = 0 := Int.natAbs_eq_zero.mp hd
      exact hk (ZMod.valMinAbs_eq_zero k |>.mp hval))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hden := stdAddChar_sub_one_norm_lower_bound k
  have hlowerpos : 0 < 4 * (d : ℝ) / q := by positivity
  calc
    ‖additiveCharacterPrefix k N‖ ≤
        2 / ‖ZMod.stdAddChar k - 1‖ :=
      additiveCharacterPrefix_norm_le k hk N
    _ ≤ 2 / (4 * (d : ℝ) / q) := by
      exact div_le_div_of_nonneg_left (by norm_num) hlowerpos hden
    _ = (q : ℝ) / (2 * k.valMinAbs.natAbs) := by
      dsimp only [d]
      field_simp
      ring

/-- The reciprocal centered frequency, extended by zero at frequency
zero. -/
noncomputable def centeredReciprocal
    {q : ℕ} [NeZero q] (k : ZMod q) : ℝ :=
  if k = 0 then 0 else ((k.valMinAbs.natAbs : ℝ)⁻¹)

/-- The sum of centered reciprocal frequencies in a natural residue
system is at most twice the corresponding harmonic number. -/
theorem centered_reciprocal_sum_nat (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Ico 1 q,
        (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic (q - 1) : ℝ) := by
  have hpoint : ∀ j ∈ Ico 1 q,
      (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
        (j : ℝ)⁻¹ + (((q - j : ℕ) : ℝ)⁻¹) := by
    intro j hj
    by_cases h : j ≤ q - j
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))
    · rw [min_eq_right (le_of_not_ge h)]
      exact le_add_of_nonneg_left (inv_nonneg.mpr (by positivity))
  calc
    ∑ j ∈ Ico 1 q, (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
        ∑ j ∈ Ico 1 q,
          ((j : ℝ)⁻¹ + (((q - j : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint j hj
    _ = (∑ j ∈ Ico 1 q, (j : ℝ)⁻¹) +
        ∑ j ∈ Ico 1 q, (((q - j : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * ∑ j ∈ Ico 1 q, (j : ℝ)⁻¹ := by
      rw [show (∑ j ∈ Ico 1 q,
          (((q - j : ℕ) : ℝ)⁻¹)) =
          ∑ j ∈ Ico 1 q, ((j : ℝ)⁻¹) by
        apply Finset.sum_bij (fun j _ ↦ q - j)
        · intro j hj
          simp only [mem_Ico] at hj ⊢
          omega
        · intro j₁ hj₁ j₂ hj₂ heq
          simp only [mem_Ico] at hj₁ hj₂
          omega
        · intro b hb
          refine ⟨q - b, ?_, ?_⟩
          · simp only [mem_Ico] at hb ⊢
            omega
          · simp only [mem_Ico] at hb
            omega
        · intro j hj
          rfl]
      ring
    _ = 2 * (harmonic (q - 1) : ℝ) := by
      congr 1
      have hset : Ico 1 q = Icc 1 (q - 1) := by
        ext j
        simp only [mem_Ico, mem_Icc]
        omega
      rw [hset, harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]

/-- The centered reciprocal sum over `ZMod q`. -/
theorem centered_reciprocal_sum_zmod (q : ℕ) [NeZero q]
    (hq : 1 ≤ q) :
    ∑ k : ZMod q, centeredReciprocal k ≤
      2 * (harmonic (q - 1) : ℝ) := by
  rw [← show (∑ i : Fin q,
      centeredReciprocal ((i : ℕ) : ZMod q)) =
      ∑ k : ZMod q, centeredReciprocal k by
        apply Fintype.sum_equiv (ZMod.finEquiv q)
        intro i
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q =>
            exact congrArg centeredReciprocal
              (@ZMod.natCast_zmod_val (q + 1) inferInstance
                ((i : Fin (q + 1)) : ZMod (q + 1)))]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => centeredReciprocal (j : ZMod q)) q]
  have hpoint (j : ℕ) (hj : j < q) :
      centeredReciprocal (j : ZMod q) =
        if j = 0 then 0 else
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
    unfold centeredReciprocal
    have hzero : (j : ZMod q) = 0 ↔ j = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      constructor
      · intro hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hj
      · intro h
        simp [h]
    rw [if_congr hzero (by rfl) (by rfl)]
    split
    · rfl
    · rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast,
        Nat.mod_eq_of_lt hj]
  calc
    ∑ j ∈ range q, centeredReciprocal (j : ZMod q) =
        ∑ j ∈ range q, if j = 0 then 0 else
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint j (mem_range.mp hj)
    _ = ∑ j ∈ Ico 1 q,
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
      have hrange : range q = insert 0 (Ico 1 q) := by
        ext j
        simp only [mem_range, mem_insert, mem_Ico]
        omega
      rw [hrange, sum_insert (by simp), if_pos rfl, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by
        intro h
        subst j
        simpa using hj
      rw [if_neg hj0]
    _ ≤ 2 * (harmonic (q - 1) : ℝ) :=
      centered_reciprocal_sum_nat q hq

/-- Pólya--Vinogradov in a sharp harmonic-number form.  The estimate is
uniform in the prefix length. -/
theorem primitive_character_prefix_sum_norm_le_harmonic
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤
      Real.sqrt q * (harmonic (q - 1) : ℝ) := by
  letI : Fact (1 < q) := ⟨by omega⟩
  rw [primitive_character_prefix_fourier hχ]
  calc
    ‖∑ k : ZMod q, (q : ℂ)⁻¹ * χ⁻¹ (-k) *
        gaussSum χ ZMod.stdAddChar * additiveCharacterPrefix k N‖ ≤
        ∑ k : ZMod q, ‖(q : ℂ)⁻¹ * χ⁻¹ (-k) *
          gaussSum χ ZMod.stdAddChar *
            additiveCharacterPrefix k N‖ := norm_sum_le _ _
    _ ≤ ∑ k : ZMod q,
        Real.sqrt q / 2 * centeredReciprocal k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [MulChar.map_nonunit _ (by
          simpa only [neg_zero] using
            (not_isUnit_zero : ¬IsUnit (0 : ZMod q)))]
        simp [centeredReciprocal]
      · have hprefix :=
          additiveCharacterPrefix_norm_le_centered k hk0 N
        have hchar : ‖χ⁻¹ (-k)‖ ≤ 1 :=
          DirichletCharacter.norm_le_one _ _
        have hqpos : (0 : ℝ) < q := by
          exact_mod_cast NeZero.pos q
        have hdpos : (0 : ℝ) < k.valMinAbs.natAbs := by
          exact_mod_cast (show 0 < k.valMinAbs.natAbs by
            rw [Nat.pos_iff_ne_zero]
            intro hd
            have hval : k.valMinAbs = 0 :=
              Int.natAbs_eq_zero.mp hd
            exact hk0 (ZMod.valMinAbs_eq_zero k |>.mp hval))
        rw [norm_mul, norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast, norm_primitive_gaussSum hχ]
        rw [centeredReciprocal, if_neg hk0]
        calc
          (q : ℝ)⁻¹ * ‖χ⁻¹ (-k)‖ * Real.sqrt q *
              ‖additiveCharacterPrefix k N‖ ≤
              (q : ℝ)⁻¹ * 1 * Real.sqrt q *
                ((q : ℝ) / (2 * k.valMinAbs.natAbs)) := by
            gcongr
          _ = Real.sqrt q / 2 *
                ((k.valMinAbs.natAbs : ℝ)⁻¹) := by
            field_simp
    _ = Real.sqrt q / 2 *
        ∑ k : ZMod q, centeredReciprocal k := by
      rw [Finset.mul_sum]
    _ ≤ Real.sqrt q / 2 *
        (2 * (harmonic (q - 1) : ℝ)) := by
      gcongr
      exact centered_reciprocal_sum_zmod q (by omega)
    _ = Real.sqrt q * (harmonic (q - 1) : ℝ) := by ring

/-- The logarithmic Pólya--Vinogradov form used for partial summation.
The explicit constant is immaterial for Lemma 6. -/
theorem primitive_character_prefix_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) := by
  have hq1 : 1 ≤ q := by omega
  have hqm1pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < q - 1)
  have hargpos : (0 : ℝ) < 2 * q := by positivity
  have hlogmono : Real.log (q - 1 : ℕ) ≤
      Real.log (2 * q : ℕ) := by
    exact Real.log_le_log hqm1pos (by exact_mod_cast (show q - 1 ≤ 2 * q by omega))
  have hlogtwo : Real.log 2 ≤ Real.log (2 * q : ℕ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ 2 * q by omega))
  have hone : (1 : ℝ) ≤ 2 * Real.log (2 * q : ℕ) := by
    nlinarith [Real.log_two_gt_d9]
  have hharm := harmonic_le_one_add_log (q - 1)
  have hH : (harmonic (q - 1) : ℝ) ≤
      3 * Real.log (2 * q : ℕ) := by
    linarith
  calc
    ‖∑ n ∈ range N, χ n‖ ≤
        Real.sqrt q * (harmonic (q - 1) : ℝ) :=
      primitive_character_prefix_sum_norm_le_harmonic hχ hq N
    _ ≤ Real.sqrt q * (3 * Real.log (2 * q : ℕ)) := by
      gcongr
    _ = 3 * Real.sqrt q * Real.log (2 * q) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring

end Chen
