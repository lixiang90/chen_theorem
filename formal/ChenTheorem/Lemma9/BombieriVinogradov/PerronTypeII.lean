import ChenTheorem.Lemma9.BombieriVinogradov.DyadicTypeII
import PrimeNumberTheoremAnd.PerronFormula

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# An exact Perron replacement for the Type-II boundary

The absolutely convergent Perron kernel `1 / (s * (s + 1))` represents the
triangular cutoff `(1 - n / X)₊`.  Its boundary value at `X/n=1` is zero.
Consequently, taking the difference at the adjacent integer endpoints `x+1`
and `x` recovers the sharp cutoff at every integer with no boundary term.
Combining the two Perron integrands before taking norms retains the
cancellation which removes the otherwise fatal extra factor of `x`.
-/

/-- The normalized triangular cutoff represented by the absolutely
convergent Perron kernel. -/
noncomputable def perronTriangularWeight (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < X then 1 - (n : ℝ) / X else 0

theorem perronTriangularWeight_nonneg
    {X : ℝ} {n : ℕ} (hX : 0 < X) :
    0 ≤ perronTriangularWeight X n := by
  unfold perronTriangularWeight
  split_ifs with h
  · exact sub_nonneg.mpr ((div_le_one hX).2 h.le)
  · exact le_rfl

theorem perron_f_one_re (t : ℝ) :
    (Perron.f 1 ((1 : ℂ) + (t : ℂ) * Complex.I)).re =
      1 / (1 + t ^ 2) - 2 / (4 + t ^ 2) := by
  unfold Perron.f
  norm_num only [Complex.ofReal_one]
  rw [Complex.one_cpow, Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div,
    add_zero, Complex.normSq_mul]
  have hn1 : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I) =
      1 + t ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  have hn2 : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I + 1) =
      4 + t ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  rw [hn1, hn2]
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re,
    Complex.mul_im, Complex.add_im, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  field_simp
  ring

theorem perron_f_one_im (t : ℝ) :
    (Perron.f 1 ((1 : ℂ) + (t : ℂ) * Complex.I)).im =
      -3 * t / ((1 + t ^ 2) * (4 + t ^ 2)) := by
  unfold Perron.f
  norm_num only [Complex.ofReal_one]
  rw [Complex.one_cpow, Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_div,
    zero_sub, Complex.normSq_mul]
  have hn1 : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I) =
      1 + t ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  have hn2 : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I + 1) =
      4 + t ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  rw [hn1, hn2]
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re,
    Complex.mul_im, Complex.add_im, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  field_simp
  ring

theorem integral_inv_four_add_sq :
    (∫ t : ℝ, (4 + t ^ 2)⁻¹) = Real.pi / 2 := by
  let g : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹
  have hscale :=
    MeasureTheory.Measure.integral_comp_mul_left g (1 / 2 : ℝ)
  calc
    (∫ t : ℝ, (4 + t ^ 2)⁻¹) =
        (1 / 4 : ℝ) * ∫ t : ℝ, g ((1 / 2 : ℝ) * t) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      dsimp only [g]
      field_simp
      ring
    _ = (1 / 4 : ℝ) * (|(1 / 2 : ℝ)⁻¹| * ∫ u : ℝ, g u) := by
      rw [hscale]
      rfl
    _ = Real.pi / 2 := by
      rw [show (∫ u : ℝ, g u) = Real.pi by
        exact integral_univ_inv_one_add_sq]
      norm_num
      ring

theorem integrable_inv_four_add_sq :
    MeasureTheory.Integrable (fun t : ℝ => (4 + t ^ 2)⁻¹) := by
  let g : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹
  have hcomp : MeasureTheory.Integrable
      (fun t : ℝ => g ((1 / 2 : ℝ) * t)) :=
    integrable_inv_one_add_sq.comp_mul_left' (by norm_num)
  have hscaled := hcomp.const_mul (1 / 4 : ℝ)
  apply hscaled.congr
  filter_upwards with t
  dsimp only [g]
  field_simp
  ring

/-- The absolutely convergent Perron kernel vanishes at its continuous
boundary value `X/n=1`. -/
theorem perronFormulaOne : VerticalIntegral' (Perron.f 1) 1 = 0 := by
  let F : ℝ → ℂ := fun t =>
    Perron.f 1 ((1 : ℂ) + (t : ℂ) * Complex.I)
  have hf : MeasureTheory.Integrable F := by
    dsimp only [F]
    exact Perron.isIntegrable (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (1 : ℝ) ≠ -1)
  have hre : (∫ t : ℝ, (F t).re) = 0 := by
    calc
      (∫ t : ℝ, (F t).re) =
          ∫ t : ℝ, (1 + t ^ 2)⁻¹ - 2 * (4 + t ^ 2)⁻¹ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        dsimp only [F]
        rw [perron_f_one_re]
        ring
      _ = (∫ t : ℝ, (1 + t ^ 2)⁻¹) -
          ∫ t : ℝ, 2 * (4 + t ^ 2)⁻¹ := by
        rw [MeasureTheory.integral_sub integrable_inv_one_add_sq
          (integrable_inv_four_add_sq.const_mul 2)]
      _ = Real.pi - 2 * (Real.pi / 2) := by
        rw [integral_univ_inv_one_add_sq,
          MeasureTheory.integral_const_mul, integral_inv_four_add_sq]
      _ = 0 := by ring
  have him : (∫ t : ℝ, (F t).im) = 0 := by
    have hneg := (MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding (fun t : ℝ => (F t).im)
    have hodd : (fun t : ℝ => (F (-t)).im) = fun t => -(F t).im := by
      funext t
      dsimp only [F]
      rw [perron_f_one_im (-t), perron_f_one_im t]
      ring
    rw [hodd, MeasureTheory.integral_neg] at hneg
    linarith
  have hz : (∫ t : ℝ, F t) = 0 := by
    apply Complex.ext
    · calc
        (∫ t : ℝ, F t).re = ∫ t : ℝ, (F t).re := (integral_re hf).symm
        _ = 0 := hre
        _ = (0 : ℂ).re := rfl
    · calc
        (∫ t : ℝ, F t).im = ∫ t : ℝ, (F t).im := (integral_im hf).symm
        _ = 0 := him
        _ = (0 : ℂ).im := rfl
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, Complex.ofReal_one]
  rw [show (∫ t : ℝ,
      Perron.f 1 ((1 : ℂ) + (t : ℂ) * Complex.I)) = 0 by exact hz]
  ring

/-- The boundary value in Perron's triangular formula is zero on every
positive vertical line, not only on `Re s = 1`. -/
theorem perronFormulaOne_at {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegral' (Perron.f 1) σ = 0 := by
  have hpull :
      VerticalIntegral (Perron.f 1) σ =
        VerticalIntegral (Perron.f 1) 1 := by
    exact Perron.contourPull (x := (1 : ℝ)) (by norm_num)
      (Set.notMem_uIcc_of_lt hσ (by norm_num))
      (Set.notMem_uIcc_of_lt (by linarith) (by norm_num))
  have hbase := perronFormulaOne
  unfold VerticalIntegral' at hbase ⊢
  rw [hpull]
  exact hbase

/-- The adjacent integral endpoints used to recover the sharp integer
cutoff from triangular weights. -/
noncomputable def perronUpperPoint (x : ℕ) : ℝ := (x : ℝ) + 1

noncomputable def perronLowerPoint (x : ℕ) : ℝ := x

theorem perronLowerPoint_pos {x : ℕ} (hx : 1 ≤ x) :
    0 < perronLowerPoint x := by
  unfold perronLowerPoint
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  positivity

theorem perronUpperPoint_pos (x : ℕ) :
    0 < perronUpperPoint x := by
  unfold perronUpperPoint
  positivity

/-- Exact recovery of the sharp cutoff on the integer lattice. -/
theorem sharpIndicator_eq_perronTriangularDifference
    (x n : ℕ) (hx : 1 ≤ x) :
    (if n ≤ x then (1 : ℝ) else 0) =
      perronUpperPoint x *
          perronTriangularWeight (perronUpperPoint x) n -
        perronLowerPoint x *
          perronTriangularWeight (perronLowerPoint x) n := by
  have hlower : 0 < perronLowerPoint x := perronLowerPoint_pos hx
  have hupper : 0 < perronUpperPoint x := perronUpperPoint_pos x
  by_cases hnlt : n < x
  · have hnle : n ≤ x := hnlt.le
    have hnu : (n : ℝ) < perronUpperPoint x := by
      unfold perronUpperPoint
      have hnx : (n : ℝ) < x := by exact_mod_cast hnlt
      linarith
    have hnl : (n : ℝ) < perronLowerPoint x := by
      unfold perronLowerPoint
      have hnx : (n : ℝ) + 1 ≤ x := by
        exact_mod_cast (show n + 1 ≤ x by omega)
      linarith
    rw [if_pos hnle]
    simp only [perronTriangularWeight, if_pos hnu, if_pos hnl]
    field_simp [hupper.ne', hlower.ne']
    unfold perronUpperPoint perronLowerPoint
    ring
  · by_cases hne : n = x
    · subst n
      have hxu : (x : ℝ) < perronUpperPoint x := by
        unfold perronUpperPoint
        linarith
      have hxl : ¬(x : ℝ) < perronLowerPoint x := by
        unfold perronLowerPoint
        simp
      simp only [le_rfl, ↓reduceIte, perronTriangularWeight, hxu, hxl]
      field_simp [hupper.ne']
      unfold perronUpperPoint
      ring
    · have hxlt : x < n := by omega
      have hnle : ¬n ≤ x := Nat.not_le.mpr hxlt
      have hnu : ¬(n : ℝ) < perronUpperPoint x := by
        unfold perronUpperPoint
        have hnx : (x : ℝ) + 1 ≤ n := by
          exact_mod_cast (show x + 1 ≤ n by omega)
        linarith
      have hnl : ¬(n : ℝ) < perronLowerPoint x := by
        unfold perronLowerPoint
        have hnx : (x : ℝ) < n := by exact_mod_cast hxlt
        linarith
      simp [hnle, perronTriangularWeight, hnu, hnl]

/-- Perron's absolutely convergent kernel represents the triangular weight
at every nonboundary positive integer. -/
theorem perronTriangularWeight_eq_verticalIntegral
    {X : ℝ} {n : ℕ} (hX : 0 < X) (hn : 1 ≤ n)
    (hne : (n : ℝ) ≠ X) :
    (perronTriangularWeight X n : ℂ) =
      VerticalIntegral' (Perron.f (X / n)) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases hlt : (n : ℝ) < X
  · rw [perronTriangularWeight, if_pos hlt]
    have hy : 1 < X / (n : ℝ) := (one_lt_div hnR).2 hlt
    rw [Perron.formulaGtOne hy (by norm_num : (0 : ℝ) < 1)]
    push_cast
    field_simp [hX.ne', hnR.ne']
  · have hgt : X < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    have hypos : 0 < X / (n : ℝ) := div_pos hX hnR
    have hylt : X / (n : ℝ) < 1 := (div_lt_one hnR).2 hgt
    rw [perronTriangularWeight, if_neg hlt]
    unfold VerticalIntegral'
    rw [Perron.formulaLtOne hypos hylt (by norm_num : (0 : ℝ) < 1)]
    simp

/-- The triangular Perron formula at an integral endpoint.  The only new
case is `n=X`, supplied by `perronFormulaOne`. -/
theorem perronTriangularWeight_nat_eq_verticalIntegral
    (X n : ℕ) (hX : 1 ≤ X) (hn : 1 ≤ n) :
    (perronTriangularWeight (X : ℝ) n : ℂ) =
      VerticalIntegral' (Perron.f ((X : ℝ) / n)) 1 := by
  rcases lt_trichotomy n X with hlt | heq | hgt
  · apply perronTriangularWeight_eq_verticalIntegral
      (by exact_mod_cast (show 0 < X by omega)) hn
    exact_mod_cast hlt.ne
  · subst n
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    simpa [perronTriangularWeight, hX0] using perronFormulaOne
  · apply perronTriangularWeight_eq_verticalIntegral
      (by exact_mod_cast (show 0 < X by omega)) hn
    exact_mod_cast hgt.ne'

/-- Perron's triangular formula at an integral endpoint on an arbitrary
positive line.  This is the form needed for the small-conductor explicit
formula, whose initial line is `1 + 1 / log x`. -/
theorem perronTriangularWeight_nat_eq_verticalIntegral_at
    (X n : ℕ) (hX : 1 ≤ X) (hn : 1 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) :
    (perronTriangularWeight (X : ℝ) n : ℂ) =
      VerticalIntegral' (Perron.f ((X : ℝ) / n)) σ := by
  rcases lt_trichotomy n X with hlt | heq | hgt
  · have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hy : (1 : ℝ) < (X : ℝ) / n := by
      apply (one_lt_div hnR).2
      exact_mod_cast hlt
    rw [perronTriangularWeight, if_pos (by exact_mod_cast hlt)]
    rw [Perron.formulaGtOne hy hσ]
    push_cast
    field_simp [hXR.ne', hnR.ne']
  · subst n
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    simpa [perronTriangularWeight, hX0] using perronFormulaOne_at hσ
  · have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hypos : (0 : ℝ) < (X : ℝ) / n := div_pos hXR hnR
    have hylt : (X : ℝ) / n < 1 := by
      apply (div_lt_one hnR).2
      exact_mod_cast hgt
    rw [perronTriangularWeight, if_neg (by exact_mod_cast (Nat.not_lt.mpr hgt.le))]
    unfold VerticalIntegral'
    rw [Perron.formulaLtOne hypos hylt hσ]
    simp

/-- A triangularly weighted Type-II rectangle. -/
noncomputable def perronTriangularTypeIIRectangle {q : ℕ}
    (X : ℝ) (U M N K L : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc M (M + N),
    ∑ m ∈ Finset.Ioc K (K + L),
      (vaughanTypeIILeftCoefficient U l : ℂ) *
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
          (X * perronTriangularWeight X (l * m) : ℝ)

/-- The separated Perron integrand for a triangular Type-II rectangle. -/
noncomputable def perronTriangularRectangleIntegrand {q : ℕ}
    (X : ℝ) (U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) : ℂ :=
  (X : ℂ) * Perron.f X s * typeIISpectralRectangle U M N K L s χ

/-- Algebraic separation of the finite Perron sum on one rectangle. -/
theorem sum_typeII_perron_summands_eq_rectangleIntegrand
    {q : ℕ} {X : ℝ} (hX : 0 < X)
    (U M N K L : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (∑ l ∈ Finset.Ioc M (M + N),
      ∑ m ∈ Finset.Ioc K (K + L),
        ((X : ℂ) *
          ((vaughanTypeIILeftCoefficient U l : ℂ) *
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
          Perron.f (X / ((l : ℝ) * m)) s) =
      perronTriangularRectangleIntegrand X U M N K L χ s := by
  rw [perronTriangularRectangleIntegrand,
    typeIISpectralRectangle_eq_bilinear, bilinearCharacterRectangle]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hlpos : 0 < l := by
    have := (Finset.mem_Ioc.mp hl).1
    omega
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hprodpos : 0 < (l : ℝ) * m := by positivity
  have hfactor := Perron.f_mul_eq_f
    (tpos := hX) (xpos := hprodpos) s
  unfold typeIISpectralLeft typeIISpectralLambda
  rw [map_mul]
  rw [← hfactor]
  have hlne : (l : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hlpos.ne'))
  have hmne : (m : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hmpos.ne'))
  have hmul : ((l : ℂ) * (m : ℂ)) ^ (-s) =
      (l : ℂ) ^ (-s) * (m : ℂ) ^ (-s) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg l) (Nat.cast_nonneg m) (-s))
  rw [show ((((l : ℝ) * m : ℝ) : ℂ)) = (l : ℂ) * (m : ℂ) by
      push_cast
      rfl,
    hmul,
    Complex.cpow_neg, Complex.cpow_neg]
  field_simp [hlne, hmne]

theorem integrable_perronTriangularRectangleIntegrand
    {q : ℕ} {X : ℝ} (hX : 0 < X)
    (U M N K L : ℕ) (χ : DirichletCharacter ℂ q) :
    MeasureTheory.Integrable (fun t : ℝ =>
      perronTriangularRectangleIntegrand X U M N K L χ
        ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hsummand (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      MeasureTheory.Integrable (fun t : ℝ =>
        ((X : ℂ) *
          ((vaughanTypeIILeftCoefficient U l : ℂ) *
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
          Perron.f (X / ((l : ℝ) * m))
            ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hy : 0 < X / ((l : ℝ) * m) := by positivity
    have hbase := Perron.isIntegrable hy
      (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (1 : ℝ) ≠ -1)
    simpa only [Complex.ofReal_one] using
      hbase.const_mul
        ((X : ℂ) *
          ((vaughanTypeIILeftCoefficient U l : ℂ) *
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)))
  have hsum : MeasureTheory.Integrable (fun t : ℝ =>
      ∑ l ∈ Finset.Ioc M (M + N),
        ∑ m ∈ Finset.Ioc K (K + L),
          ((X : ℂ) *
            ((vaughanTypeIILeftCoefficient U l : ℂ) *
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
            Perron.f (X / ((l : ℝ) * m))
              ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    apply MeasureTheory.integrable_finsetSum
    intro l hl
    apply MeasureTheory.integrable_finsetSum
    intro m hm
    exact hsummand l hl m hm
  apply hsum.congr
  filter_upwards with t
  exact sum_typeII_perron_summands_eq_rectangleIntegrand
    hX U M N K L χ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- A triangular Type-II rectangle is exactly its absolutely convergent
Perron vertical integral whenever the scalar triangular formula is supplied
at every positive integer in the rectangle. -/
theorem perronTriangularTypeIIRectangle_eq_verticalIntegral
    {q : ℕ} {X : ℝ} (hX : 0 < X)
    (hweight : ∀ n : ℕ, 1 ≤ n →
      (perronTriangularWeight X n : ℂ) =
        VerticalIntegral' (Perron.f (X / n)) 1)
    (U M N K L : ℕ) (χ : DirichletCharacter ℂ q) :
    perronTriangularTypeIIRectangle X U M N K L χ =
      VerticalIntegral'
        (perronTriangularRectangleIntegrand X U M N K L χ) 1 := by
  let F : ℕ → ℕ → ℝ → ℂ := fun l m t =>
    ((X : ℂ) *
      ((vaughanTypeIILeftCoefficient U l : ℂ) *
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
      Perron.f (X / ((l : ℝ) * m)) ((1 : ℂ) + (t : ℂ) * Complex.I)
  have hFint (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      MeasureTheory.Integrable (F l m) := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hy : 0 < X / ((l : ℝ) * m) := by positivity
    have hbase := Perron.isIntegrable hy
      (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (1 : ℝ) ≠ -1)
    simpa only [F, Complex.ofReal_one] using
      hbase.const_mul
        ((X : ℂ) *
          ((vaughanTypeIILeftCoefficient U l : ℂ) *
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)))
  have hpoint (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (X * perronTriangularWeight X (l * m) : ℝ) =
        VerticalIntegral' (fun s : ℂ =>
          ((X : ℂ) *
            ((vaughanTypeIILeftCoefficient U l : ℂ) *
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
            Perron.f (X / ((l : ℝ) * m)) s) 1 := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hlm : 1 ≤ l * m := Nat.mul_pos hlpos hmpos
    have hweight : (perronTriangularWeight X (l * m) : ℂ) =
        VerticalIntegral' (Perron.f (X / ((l : ℝ) * m))) 1 := by
      simpa only [Nat.cast_mul] using hweight (l * m) hlm
    rw [show ((X * perronTriangularWeight X (l * m) : ℝ) : ℂ) =
        (X : ℂ) * (perronTriangularWeight X (l * m) : ℂ) by
          push_cast
          rfl,
      hweight]
    unfold VerticalIntegral' VerticalIntegral
    simp only [smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    push_cast
    ring
  rw [perronTriangularTypeIIRectangle]
  calc
    (∑ l ∈ Finset.Ioc M (M + N),
      ∑ m ∈ Finset.Ioc K (K + L),
        (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (X * perronTriangularWeight X (l * m) : ℝ)) =
        ∑ l ∈ Finset.Ioc M (M + N),
          ∑ m ∈ Finset.Ioc K (K + L),
            VerticalIntegral' (fun s : ℂ =>
              ((X : ℂ) *
                ((vaughanTypeIILeftCoefficient U l : ℂ) *
                  (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
                Perron.f (X / ((l : ℝ) * m)) s) 1 := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro m hm
      exact hpoint l hl m hm
    _ = VerticalIntegral' (fun s : ℂ =>
          ∑ l ∈ Finset.Ioc M (M + N),
            ∑ m ∈ Finset.Ioc K (K + L),
              ((X : ℂ) *
                ((vaughanTypeIILeftCoefficient U l : ℂ) *
                  (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))) *
                Perron.f (X / ((l : ℝ) * m)) s) 1 := by
      unfold VerticalIntegral' VerticalIntegral
      simp only [smul_eq_mul]
      have hsumIntegral :
          (∑ l ∈ Finset.Ioc M (M + N),
            ∑ m ∈ Finset.Ioc K (K + L), ∫ t : ℝ, F l m t) =
            ∫ t : ℝ, ∑ l ∈ Finset.Ioc M (M + N),
              ∑ m ∈ Finset.Ioc K (K + L), F l m t := by
        rw [MeasureTheory.integral_finsetSum (Finset.Ioc M (M + N))]
        · apply Finset.sum_congr rfl
          intro l hl
          exact (MeasureTheory.integral_finsetSum
            (Finset.Ioc K (K + L)) (hFint l hl)).symm
        · intro l hl
          exact MeasureTheory.integrable_finsetSum
            (Finset.Ioc K (K + L)) (hFint l hl)
      change (∑ l ∈ Finset.Ioc M (M + N),
          ∑ m ∈ Finset.Ioc K (K + L),
            (1 / (2 * ↑Real.pi * Complex.I)) *
              (Complex.I * ∫ t : ℝ, F l m t)) = _
      simp_rw [← mul_assoc,
        ← Finset.mul_sum]
      rw [hsumIntegral]
      congr 3
      funext t
      dsimp only [F]
      simp only [Complex.ofReal_one]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = VerticalIntegral'
          (perronTriangularRectangleIntegrand X U M N K L χ) 1 := by
      congr 1
      funext s
      exact sum_typeII_perron_summands_eq_rectangleIntegrand
        hX U M N K L χ s

theorem perronUpperTypeIIRectangle_eq_verticalIntegral
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) :
    perronTriangularTypeIIRectangle (perronUpperPoint x)
        U M N K L χ =
      VerticalIntegral'
        (perronTriangularRectangleIntegrand (perronUpperPoint x)
          U M N K L χ) 1 := by
  exact perronTriangularTypeIIRectangle_eq_verticalIntegral
    (perronUpperPoint_pos x)
    (fun n hn => by
      unfold perronUpperPoint
      simpa only [Nat.cast_add, Nat.cast_one] using
        perronTriangularWeight_nat_eq_verticalIntegral (x + 1) n
          (by omega) hn)
    U M N K L χ

theorem perronLowerTypeIIRectangle_eq_verticalIntegral
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    perronTriangularTypeIIRectangle (perronLowerPoint x)
        U M N K L χ =
      VerticalIntegral'
        (perronTriangularRectangleIntegrand (perronLowerPoint x)
          U M N K L χ) 1 := by
  exact perronTriangularTypeIIRectangle_eq_verticalIntegral
    (perronLowerPoint_pos hx)
    (fun n hn => by
      unfold perronLowerPoint
      exact perronTriangularWeight_nat_eq_verticalIntegral x n hx hn)
    U M N K L χ

/-- The cancellation-preserving difference of the two neighboring Perron
integrands. -/
noncomputable def perronSharpRectangleIntegrand {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) : ℂ :=
  perronTriangularRectangleIntegrand (perronUpperPoint x)
      U M N K L χ s -
    perronTriangularRectangleIntegrand (perronLowerPoint x)
      U M N K L χ s

/-- The scalar Perron kernel in which the two neighboring triangular
cutoffs are combined before norms are taken. -/
noncomputable def perronSharpKernel (x : ℕ) (s : ℂ) : ℂ :=
  (perronUpperPoint x : ℂ) * Perron.f (perronUpperPoint x) s -
    (perronLowerPoint x : ℂ) * Perron.f (perronLowerPoint x) s

/-- The sharp Perron integrand is the cancellation-preserving scalar kernel
times the already separated Type-II spectral rectangle. -/
theorem perronSharpRectangleIntegrand_eq_kernel_mul {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    perronSharpRectangleIntegrand x U M N K L χ s =
      perronSharpKernel x s * typeIISpectralRectangle U M N K L s χ := by
  unfold perronSharpRectangleIntegrand perronTriangularRectangleIntegrand
    perronSharpKernel
  ring

theorem norm_perronSharpRectangleIntegrand_eq {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    ‖perronSharpRectangleIntegrand x U M N K L χ s‖ =
      ‖perronSharpKernel x s‖ *
        ‖typeIISpectralRectangle U M N K L s χ‖ := by
  rw [perronSharpRectangleIntegrand_eq_kernel_mul, norm_mul]

/-- On any line avoiding the two poles, the combined scalar kernel is
integrable. -/
theorem integrable_perronSharpKernel (x : ℕ) (hx : 1 ≤ x)
    (σ : ℝ) (hσ0 : σ ≠ 0) (hσ1 : σ ≠ -1) :
    MeasureTheory.Integrable (fun t : ℝ =>
      perronSharpKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hu := (Perron.isIntegrable (perronUpperPoint_pos x) hσ0 hσ1).const_mul
    (perronUpperPoint x : ℂ)
  have hl := (Perron.isIntegrable (perronLowerPoint_pos hx) hσ0 hσ1).const_mul
    (perronLowerPoint x : ℂ)
  change MeasureTheory.Integrable
    ((fun t : ℝ => (perronUpperPoint x : ℂ) *
        Perron.f (perronUpperPoint x) ((σ : ℂ) + (t : ℂ) * Complex.I)) -
      fun t : ℝ => (perronLowerPoint x : ℂ) *
        Perron.f (perronLowerPoint x) ((σ : ℂ) + (t : ℂ) * Complex.I))
  exact hu.sub hl

/-- The cancellation in the sharp kernel is exactly the integral of
`u^s` across the unit interval between the two half-integers. -/
theorem perronSharpKernel_eq_intervalIntegral_div
    (x : ℕ) (hx : 1 ≤ x) (s : ℂ) (hs0 : s ≠ 0)
    (hsre : -1 < s.re) :
    perronSharpKernel x s =
      (∫ u : ℝ in perronLowerPoint x..perronUpperPoint x,
          (u : ℂ) ^ s) / s := by
  have hu0 : (perronUpperPoint x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (perronUpperPoint_pos x).ne'
  have hl0 : (perronLowerPoint x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (perronLowerPoint_pos hx).ne'
  have hs1 : s + 1 ≠ 0 := by
    intro h
    apply_fun Complex.re at h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hupper :
      (perronUpperPoint x : ℂ) *
          (perronUpperPoint x : ℂ) ^ s =
        (perronUpperPoint x : ℂ) ^ (s + 1) := by
    rw [Complex.cpow_add s 1 hu0, Complex.cpow_one]
    ring
  have hlower :
      (perronLowerPoint x : ℂ) *
          (perronLowerPoint x : ℂ) ^ s =
        (perronLowerPoint x : ℂ) ^ (s + 1) := by
    rw [Complex.cpow_add s 1 hl0, Complex.cpow_one]
    ring
  rw [integral_cpow (a := perronLowerPoint x)
      (b := perronUpperPoint x) (r := s) (Or.inl hsre)]
  unfold perronSharpKernel Perron.f
  simp only [← mul_div_assoc]
  rw [hupper, hlower]
  field_simp [hs0, hs1]

/-- The cancellation bound for the sharp kernel on `Re s = 1`.  This is the
low-frequency estimate; its denominator has only one power of `|s|`. -/
theorem norm_perronSharpKernel_one_add_mul_I_le
    (x : ℕ) (hx : 1 ≤ x) (t : ℝ) :
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      perronUpperPoint x /
        ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] at hs
    norm_num at hs
  have hsre : -1 < s.re := by
    simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero]
    norm_num
  have hlowerUpper : perronLowerPoint x ≤ perronUpperPoint x := by
    unfold perronLowerPoint perronUpperPoint
    linarith
  have hinterval :
      ‖∫ u : ℝ in perronLowerPoint x..perronUpperPoint x,
          (u : ℂ) ^ s‖ ≤ perronUpperPoint x := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := perronLowerPoint x) (b := perronUpperPoint x)
      (C := perronUpperPoint x) (f := fun u : ℝ => (u : ℂ) ^ s)
      (fun u hu => by
        rw [Set.uIoc_of_le hlowerUpper] at hu
        have hulower : perronLowerPoint x < u := hu.1
        have hupos : 0 < u := (perronLowerPoint_pos hx).trans hulower
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
        simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
          Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_one]
        exact hu.2)
    have hlength :
        |perronUpperPoint x - perronLowerPoint x| = 1 := by
      unfold perronUpperPoint perronLowerPoint
      rw [abs_of_nonneg]
      · ring
      · linarith
    simpa only [hlength, mul_one] using hconst
  rw [perronSharpKernel_eq_intervalIntegral_div x hx s hs0 hsre,
    norm_div]
  exact div_le_div_of_nonneg_right hinterval (norm_nonneg s)

/-- A convenient globally integrable low-frequency majorant for the sharp
kernel.  The loss of `2` replaces `‖1+it‖` by `1+|t|`. -/
theorem norm_perronSharpKernel_one_add_mul_I_le_two_div
    (x : ℕ) (hx : 1 ≤ x) (t : ℝ) :
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * perronUpperPoint x / (1 + |t|) := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] at hs
    norm_num at hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hre : 1 ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    simpa only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, abs_one] using h
  have him : |t| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa only [s, Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, zero_add] using h
  have hden : 1 + |t| ≤ 2 * ‖s‖ := by linarith
  have hdenpos : 0 < 1 + |t| := by positivity
  calc
    ‖perronSharpKernel x s‖ ≤ perronUpperPoint x / ‖s‖ :=
      norm_perronSharpKernel_one_add_mul_I_le x hx t
    _ ≤ 2 * perronUpperPoint x / (1 + |t|) := by
      apply (div_le_div_iff₀ hspos hdenpos).2
      have hupper : 0 ≤ perronUpperPoint x := (perronUpperPoint_pos x).le
      nlinarith

theorem norm_real_mul_perron_f_one_add_mul_I
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ‖(X : ℂ) * Perron.f X ((1 : ℂ) + (t : ℂ) * Complex.I)‖ =
      X ^ 2 /
        (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖(1 : ℂ) + (t : ℂ) * Complex.I + 1‖) := by
  unfold Perron.f
  rw [norm_mul, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [Complex.norm_real,
    Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
    sub_self, add_zero, Real.rpow_one]
  rw [Real.norm_of_nonneg hX.le]
  ring

/-- Away from zero frequency one may discard the cancellation and retain
the original quadratic Perron decay. -/
theorem norm_perronSharpKernel_one_add_mul_I_le_sq_div
    (x : ℕ) (hx : 1 ≤ x) (t : ℝ) (ht : 0 < |t|) :
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / t ^ 2 := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] at hs
    norm_num at hs
  have hs1 : s + 1 ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] at hs
    norm_num at hs
  have him : |t| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa only [s, Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, zero_add] using h
  have him1 : |t| ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    simpa only [s, Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, zero_add] using h
  have hden : t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [sq, ← abs_mul_abs_self]
    exact mul_le_mul him him1 (abs_nonneg t) (norm_nonneg s)
  have ht2 : 0 < t ^ 2 := by
    rw [sq_pos_iff]
    exact abs_pos.mp ht
  have hupper := norm_real_mul_perron_f_one_add_mul_I
    (perronUpperPoint_pos x) t
  have hlower := norm_real_mul_perron_f_one_add_mul_I
    (perronLowerPoint_pos hx) t
  unfold perronSharpKernel
  calc
    ‖(perronUpperPoint x : ℂ) * Perron.f (perronUpperPoint x) s -
        (perronLowerPoint x : ℂ) * Perron.f (perronLowerPoint x) s‖ ≤
        ‖(perronUpperPoint x : ℂ) * Perron.f (perronUpperPoint x) s‖ +
          ‖(perronLowerPoint x : ℂ) * Perron.f (perronLowerPoint x) s‖ :=
      norm_sub_le _ _
    _ = perronUpperPoint x ^ 2 / (‖s‖ * ‖s + 1‖) +
          perronLowerPoint x ^ 2 / (‖s‖ * ‖s + 1‖) := by
      simpa only [s] using congrArg₂ (· + ·) hupper hlower
    _ = (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (‖s‖ * ‖s + 1‖) := by ring
    _ ≤ (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / t ^ 2 := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact ht2
      · exact hden

/-- Elementary logarithmic mass of the low-frequency majorant. -/
theorem intervalIntegral_inv_one_add_abs (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in -T..T, 1 / (1 + |t|)) =
      2 * Real.log (1 + T) := by
  let f : ℝ → ℝ := fun t => 1 / (1 + |t|)
  have hf : Continuous f := by
    dsimp only [f]
    exact continuous_const.div (continuous_const.add continuous_abs)
      (fun t => by positivity)
  have hpos : (∫ t : ℝ in 0..T, f t) = Real.log (1 + T) := by
    calc
      (∫ t : ℝ in 0..T, f t) = ∫ t : ℝ in 0..T, 1 / (1 + t) := by
        apply intervalIntegral.integral_congr
        intro t htmem
        rw [Set.uIcc_of_le hT] at htmem
        simp only [f, abs_of_nonneg htmem.1]
      _ = ∫ u : ℝ in 1..T + 1, 1 / u := by
        convert (intervalIntegral.integral_comp_add_right
          (f := fun u : ℝ => 1 / u) (a := 0) (b := T) 1) using 1 <;>
          ring_nf
      _ = Real.log ((T + 1) / 1) :=
        integral_one_div_of_pos (by norm_num) (by linarith)
      _ = Real.log (1 + T) := by ring_nf
  have heven (t : ℝ) : f (-t) = f t := by
    simp only [f, abs_neg]
  have hneg : (∫ t : ℝ in -T..0, f t) = Real.log (1 + T) := by
    calc
      (∫ t : ℝ in -T..0, f t) = ∫ t : ℝ in 0..T, f (-t) := by
        symm
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := 0) (b := T))
      _ = ∫ t : ℝ in 0..T, f t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact heven t
      _ = Real.log (1 + T) := hpos
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T),
    hneg, hpos]
  ring

theorem setIntegral_Icc_inv_one_add_abs (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Icc (-T) T, 1 / (1 + |t|)) =
      2 * Real.log (1 + T) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact intervalIntegral_inv_one_add_abs T hT

theorem setIntegral_Ioi_inv_sq (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ in Set.Ioi T, 1 / t ^ 2) = 1 / T := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT
  calc
    (∫ t : ℝ in Set.Ioi T, 1 / t ^ 2) =
        ∫ t : ℝ in Set.Ioi T, t ^ (-2 : ℝ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 1 / t ^ 2 = t ^ (-2 : ℝ)
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, one_div]
    _ = -T ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) := h
    _ = 1 / T := by
      rw [show (-2 : ℝ) + 1 = -(1 : ℝ) by norm_num,
        Real.rpow_neg hT.le, Real.rpow_one]
      ring

theorem integrableOn_Ioi_inv_sq (T : ℝ) (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Set.Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ))
    (by norm_num) hT
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  change t ^ (-2 : ℝ) = 1 / t ^ 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, one_div]

theorem setIntegral_Iio_inv_sq (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ in Set.Iio (-T), 1 / t ^ 2) = 1 / T := by
  rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
  rw [← integral_comp_neg_Ioi T (fun t : ℝ => 1 / t ^ 2)]
  simp only [neg_sq]
  exact setIntegral_Ioi_inv_sq T hT

theorem integrableOn_Iio_inv_sq (T : ℝ) (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Set.Iio (-T)) := by
  have hpre : Neg.neg ⁻¹' Set.Iio (-T) = Set.Ioi T := by
    ext t
    change (-t < -T) ↔ T < t
    exact neg_lt_neg_iff
  rw [← (MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  rw [hpre]
  simp only [Function.comp_def, neg_sq]
  exact integrableOn_Ioi_inv_sq T hT

/-- On a central frequency interval, cancellation in the sharp kernel gives
only logarithmic mass. -/
theorem setIntegral_Icc_norm_perronSharpKernel_le
    (x : ℕ) (hx : 1 ≤ x) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Icc (-T) T,
        ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      4 * perronUpperPoint x * Real.log (1 + T) := by
  let f : ℝ → ℝ := fun t =>
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖
  let g : ℝ → ℝ := fun t => 2 * perronUpperPoint x / (1 + |t|)
  have hf : MeasureTheory.IntegrableOn f (Set.Icc (-T) T) :=
    (integrable_perronSharpKernel x hx 1 (by norm_num) (by norm_num)).norm.integrableOn
  have hgcont : Continuous g := by
    dsimp only [g]
    exact continuous_const.div (continuous_const.add continuous_abs)
      (fun t => by positivity)
  have hg : MeasureTheory.IntegrableOn g (Set.Icc (-T) T) :=
    hgcont.integrableOn_Icc
  calc
    (∫ t : ℝ in Set.Icc (-T) T, f t) ≤
        ∫ t : ℝ in Set.Icc (-T) T, g t := by
      exact MeasureTheory.setIntegral_mono_on hf hg measurableSet_Icc
        (fun t _ht => norm_perronSharpKernel_one_add_mul_I_le_two_div x hx t)
    _ = (2 * perronUpperPoint x) *
        ∫ t : ℝ in Set.Icc (-T) T, 1 / (1 + |t|) := by
      dsimp only [g]
      simp_rw [div_eq_mul_inv]
      rw [MeasureTheory.integral_const_mul]
      simp only [one_mul]
    _ = 4 * perronUpperPoint x * Real.log (1 + T) := by
      rw [setIntegral_Icc_inv_one_add_abs T hT]
      ring

/-- Outside a central frequency interval, the original quadratic Perron
decay makes the sharp kernel tail have mass `O(x²/T)`. -/
theorem setIntegral_compl_Icc_norm_perronSharpKernel_le
    (x : ℕ) (hx : 1 ≤ x) (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ in (Set.Icc (-T) T)ᶜ,
        ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T := by
  let f : ℝ → ℝ := fun t =>
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖
  let C : ℝ := perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2
  have hf : MeasureTheory.Integrable f :=
    (integrable_perronSharpKernel x hx 1 (by norm_num) (by norm_num)).norm
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hright : (∫ t : ℝ in Set.Ioi T, f t) ≤ C / T := by
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => C * (1 / t ^ 2))
        (Set.Ioi T) := by
      exact (integrableOn_Ioi_inv_sq T hT).const_mul C
    calc
      (∫ t : ℝ in Set.Ioi T, f t) ≤
          ∫ t : ℝ in Set.Ioi T, C * (1 / t ^ 2) := by
        exact MeasureTheory.setIntegral_mono_on hf.integrableOn hg measurableSet_Ioi
          (fun t ht => by
            dsimp only [f, C]
            simpa only [div_eq_mul_inv, one_mul] using
              norm_perronSharpKernel_one_add_mul_I_le_sq_div x hx t
                (abs_pos.mpr (ne_of_gt (hT.trans ht))))
      _ = C * ∫ t : ℝ in Set.Ioi T, 1 / t ^ 2 := by
        simp_rw [div_eq_mul_inv]
        rw [MeasureTheory.integral_const_mul]
      _ = C / T := by
        rw [setIntegral_Ioi_inv_sq T hT]
        ring
  have hleft : (∫ t : ℝ in Set.Iio (-T), f t) ≤ C / T := by
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => C * (1 / t ^ 2))
        (Set.Iio (-T)) := by
      exact (integrableOn_Iio_inv_sq T hT).const_mul C
    calc
      (∫ t : ℝ in Set.Iio (-T), f t) ≤
          ∫ t : ℝ in Set.Iio (-T), C * (1 / t ^ 2) := by
        exact MeasureTheory.setIntegral_mono_on hf.integrableOn hg measurableSet_Iio
          (fun t ht => by
            dsimp only [f, C]
            simpa only [div_eq_mul_inv, one_mul] using
              norm_perronSharpKernel_one_add_mul_I_le_sq_div x hx t
                (abs_pos.mpr (by
                  have htlt : t < -T := ht
                  have htneg : t < 0 := htlt.trans (neg_lt_zero.mpr hT)
                  exact htneg.ne)))
      _ = C * ∫ t : ℝ in Set.Iio (-T), 1 / t ^ 2 := by
        simp_rw [div_eq_mul_inv]
        rw [MeasureTheory.integral_const_mul]
      _ = C / T := by
        rw [setIntegral_Iio_inv_sq T hT]
        ring
  have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      by_cases hleft : t < -T
      · exact Or.inl hleft
      · right
        by_contra hright
        exact h ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
    · intro h hmem
      rcases h with h | h
      · exact (not_lt_of_ge hmem.1) h
      · exact (not_lt_of_ge hmem.2) h
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    apply Set.disjoint_left.2
    intro t htleft htright
    have htleft' : t < -T := htleft
    have htright' : T < t := htright
    linarith
  rw [hcompl, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      hf.integrableOn hf.integrableOn]
  dsimp only [C] at hright hleft ⊢
  calc
    (∫ t : ℝ in Set.Iio (-T), f t) + ∫ t : ℝ in Set.Ioi T, f t ≤
        (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T +
          (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T :=
      add_le_add hleft hright
    _ = 2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T := by
      ring

/-- The full sharp-kernel mass is the sum of its logarithmic central part
and its quadratically decaying tail. -/
theorem integral_norm_perronSharpKernel_le
    (x : ℕ) (hx : 1 ≤ x) (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ,
        ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      4 * perronUpperPoint x * Real.log (1 + T) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T := by
  let f : ℝ → ℝ := fun t =>
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖
  have hf : MeasureTheory.Integrable f :=
    (integrable_perronSharpKernel x hx 1 (by norm_num) (by norm_num)).norm
  calc
    (∫ t : ℝ, f t) =
        (∫ t : ℝ in Set.Icc (-T) T, f t) +
          ∫ t : ℝ in (Set.Icc (-T) T)ᶜ, f t :=
      (MeasureTheory.integral_add_compl measurableSet_Icc hf).symm
    _ ≤ 4 * perronUpperPoint x * Real.log (1 + T) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T :=
      add_le_add
        (setIntegral_Icc_norm_perronSharpKernel_le x hx T hT.le)
        (setIntegral_compl_Icc_norm_perronSharpKernel_le x hx T hT)

/-- Unsquared form of the spectral rectangle large-sieve estimate. -/
theorem typeIISpectralRectangleMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U D Q M N K L : ℕ) (s : ℂ),
        1 ≤ s.re → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖typeIISpectralRectangle U M N K L s i.2‖) ≤
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) := by
  rcases typeIISpectralRectangleMean_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hsquare⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U D Q M N K L s hs hD hDQ hM hK hMN hKL
  let S : ℝ := ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i *
      ‖typeIISpectralRectangle U M N K L s i.2‖
  let R : ℝ := typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact typeIISpectralRectangleMajorant_nonneg
      hC₀.le hC₁.le hD hM hK hMN hKL
  have hsq : S ^ 2 ≤ R := by
    simpa only [S, R] using
      hsquare U D Q M N K L s hs hD hDQ hM hK hMN hKL
  apply (sq_le_sq₀ hS (Real.sqrt_nonneg R)).1
  rw [Real.sq_sqrt hR]
  exact hsq

/-- At each height the primitive-character mean of the sharp Perron
integrand factors into the scalar kernel and the spectral majorant. -/
theorem perronSharpRectangleIntegrandMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ) (t : ℝ),
        1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖perronSharpRectangleIntegrand x U M N K L i.2
                  ((1 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
            ‖perronSharpKernel x
                ((1 : ℂ) + (t : ℂ) * Complex.I)‖ *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) := by
  rcases typeIISpectralRectangleMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hspectral⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L t hD hDQ hM hK hMN hKL
  let s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  have hsre : 1 ≤ s.re := by
    dsimp only [s]
    simp
  have hspec := hspectral U D Q M N K L s hsre hD hDQ hM hK hMN hKL
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖perronSharpRectangleIntegrand x U M N K L i.2 s‖) =
        ‖perronSharpKernel x s‖ *
          ∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖typeIISpectralRectangle U M N K L s i.2‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_perronSharpRectangleIntegrand_eq]
      ring
    _ ≤ ‖perronSharpKernel x s‖ *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) :=
      mul_le_mul_of_nonneg_left hspec (norm_nonneg _)

theorem integrable_perronSharpRectangleIntegrand
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      perronSharpRectangleIntegrand x U M N K L χ
        ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  exact (integrable_perronTriangularRectangleIntegrand
      (perronUpperPoint_pos x) U M N K L χ).sub
    (integrable_perronTriangularRectangleIntegrand
      (perronLowerPoint_pos hx) U M N K L χ)

/-- Taking norms in the sharp Perron representation leaves the integral of
the sharp scalar kernel times the spectral rectangle. -/
theorem norm_perronSharpVerticalIntegral_le
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖VerticalIntegral'
        (perronSharpRectangleIntegrand x U M N K L χ) 1‖ ≤
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          ‖perronSharpRectangleIntegrand x U M N K L χ
            ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, Complex.ofReal_one]
  calc
    ‖(1 / ((2 : ℂ) * Real.pi * Complex.I)) *
        (Complex.I *
          ∫ t : ℝ,
            perronSharpRectangleIntegrand x U M N K L χ
              ((1 : ℂ) + (t : ℂ) * Complex.I))‖ =
        (1 / (2 * Real.pi)) *
          ‖∫ t : ℝ,
            perronSharpRectangleIntegrand x U M N K L χ
              ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_mul, norm_mul, norm_div, norm_one, norm_mul, norm_mul,
        Complex.norm_I]
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]]
      ring
    _ ≤ (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          ‖perronSharpRectangleIntegrand x U M N K L χ
            ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      apply mul_le_mul_of_nonneg_left
      · exact MeasureTheory.norm_integral_le_integral_norm _
      · positivity

/-- Primitive-character mean bound for the vertical-integral part of one
sharp Type-II rectangle.  The analytic cost is exactly the scalar sharp
kernel mass. -/
theorem perronSharpVerticalIntegralMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ),
        1 ≤ x → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖VerticalIntegral'
                    (perronSharpRectangleIntegrand x U M N K L i.2) 1‖) ≤
            (1 / (2 * Real.pi)) *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
              ∫ t : ℝ,
                ‖perronSharpKernel x
                  ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rcases perronSharpRectangleIntegrandMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hpoint⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L hx hD hDQ hM hK hMN hKL
  let I := characterIndicesIoc D Q
  let G : (i : (q : ℕ) × DirichletCharacter ℂ q) → ℝ → ℝ := fun i t =>
    primitiveDyadicWeight i *
      ‖perronSharpRectangleIntegrand x U M N K L i.2
        ((1 : ℂ) + (t : ℂ) * Complex.I)‖
  let H : ℝ → ℝ := fun t =>
    ‖perronSharpKernel x ((1 : ℂ) + (t : ℂ) * Complex.I)‖ *
      Real.sqrt
        (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L)
  have hGint (i : (q : ℕ) × DirichletCharacter ℂ q) (hi : i ∈ I) :
      MeasureTheory.Integrable (G i) := by
    dsimp only [G]
    exact (integrable_perronSharpRectangleIntegrand
      x U M N K L i.2 hx).norm.const_mul (primitiveDyadicWeight i)
  have hsumInt : MeasureTheory.Integrable (fun t : ℝ => ∑ i ∈ I, G i t) :=
    MeasureTheory.integrable_finsetSum I hGint
  have hHint : MeasureTheory.Integrable H := by
    dsimp only [H]
    exact (integrable_perronSharpKernel x hx 1
      (by norm_num) (by norm_num)).norm.mul_const _
  have hmeanIntegral :
      (∫ t : ℝ, ∑ i ∈ I, G i t) ≤ ∫ t : ℝ, H t := by
    apply MeasureTheory.integral_mono hsumInt hHint
    intro t
    simpa only [I, G, H] using
      hpoint x U D Q M N K L t hD hDQ hM hK hMN hKL
  have hsumIntegral :
      (∑ i ∈ I, primitiveDyadicWeight i *
          ∫ t : ℝ,
            ‖perronSharpRectangleIntegrand x U M N K L i.2
              ((1 : ℂ) + (t : ℂ) * Complex.I)‖) =
        ∫ t : ℝ, ∑ i ∈ I, G i t := by
    rw [MeasureTheory.integral_finsetSum I hGint]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [MeasureTheory.integral_const_mul]
  have hHIntegral :
      (∫ t : ℝ, H t) =
        Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
          ∫ t : ℝ,
            ‖perronSharpKernel x
              ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    dsimp only [H]
    ring
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖VerticalIntegral'
              (perronSharpRectangleIntegrand x U M N K L i.2) 1‖) ≤
        ∑ i ∈ I, primitiveDyadicWeight i *
          ((1 / (2 * Real.pi)) *
            ∫ t : ℝ,
              ‖perronSharpRectangleIntegrand x U M N K L i.2
                ((1 : ℂ) + (t : ℂ) * Complex.I)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact norm_perronSharpVerticalIntegral_le x U M N K L i.2
      · exact primitiveDyadicWeight_nonneg i
    _ = (1 / (2 * Real.pi)) *
        ∑ i ∈ I, primitiveDyadicWeight i *
          ∫ t : ℝ,
            ‖perronSharpRectangleIntegrand x U M N K L i.2
              ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, ∑ i ∈ I, G i t := by rw [hsumIntegral]
    _ ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, H t := by
      exact mul_le_mul_of_nonneg_left hmeanIntegral (by positivity)
    _ = (1 / (2 * Real.pi)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
        ∫ t : ℝ,
          ‖perronSharpKernel x
            ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [hHIntegral]
      ring

/-- The preceding rectangle mean with the sharp-kernel mass replaced by its
explicit central-plus-tail bound. -/
theorem perronSharpVerticalIntegralMean_le_explicit :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ) (T : ℝ),
        1 ≤ x → 0 < T → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖VerticalIntegral'
                    (perronSharpRectangleIntegrand x U M N K L i.2) 1‖) ≤
            (1 / (2 * Real.pi)) *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
              (4 * perronUpperPoint x * Real.log (1 + T) +
                2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T) := by
  rcases perronSharpVerticalIntegralMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hmean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L T hx hT hD hDQ hM hK hMN hKL
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖VerticalIntegral'
              (perronSharpRectangleIntegrand x U M N K L i.2) 1‖) ≤
        (1 / (2 * Real.pi)) *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
          ∫ t : ℝ,
            ‖perronSharpKernel x
              ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
      hmean x U D Q M N K L hx hD hDQ hM hK hMN hKL
    _ ≤ (1 / (2 * Real.pi)) *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
          (4 * perronUpperPoint x * Real.log (1 + T) +
            2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / T) := by
      apply mul_le_mul_of_nonneg_left
      · exact integral_norm_perronSharpKernel_le x hx T hT
      · exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- Exact rectangle-level recovery of the sharp cutoff from two triangular
cutoffs at the adjacent integral endpoints `x` and `x+1`. -/
theorem sharpTypeIIRectangle_eq_perronDifference
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    sharpTypeIIRectangle x U M N K L χ =
      perronTriangularTypeIIRectangle (perronUpperPoint x)
          U M N K L χ -
        perronTriangularTypeIIRectangle (perronLowerPoint x)
          U M N K L χ := by
  rw [sharpTypeIIRectangle, perronTriangularTypeIIRectangle,
    perronTriangularTypeIIRectangle]
  simp_rw [sharpTypeIITerm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro m hm
  have hind := sharpIndicator_eq_perronTriangularDifference x (l * m) hx
  let B : ℂ := (vaughanTypeIILeftCoefficient U l : ℂ) *
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)
  have hleft :
      (if l * m ≤ x then B else 0) =
        B * ((if l * m ≤ x then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp
  have hindC := congrArg (fun r : ℝ => (r : ℂ)) hind
  push_cast at hindC
  change (if l * m ≤ x then B else 0) = _
  rw [hleft, hindC]
  dsimp only [B]
  push_cast
  ring

/-- Exact cancellation-preserving Perron representation of a sharp Type-II
rectangle, with no arithmetic boundary remainder. -/
theorem sharpTypeIIRectangle_eq_perronVerticalIntegral
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    sharpTypeIIRectangle x U M N K L χ =
      VerticalIntegral'
          (perronSharpRectangleIntegrand x U M N K L χ) 1 := by
  rw [sharpTypeIIRectangle_eq_perronDifference
      x U M N K L χ hx,
    perronUpperTypeIIRectangle_eq_verticalIntegral x U M N K L χ,
    perronLowerTypeIIRectangle_eq_verticalIntegral x U M N K L χ hx]
  unfold VerticalIntegral' VerticalIntegral perronSharpRectangleIntegrand
  simp only [smul_eq_mul, Complex.ofReal_one]
  have hsub :
      (∫ t : ℝ,
          perronTriangularRectangleIntegrand (perronUpperPoint x)
              U M N K L χ ((1 : ℂ) + (t : ℂ) * Complex.I) -
            perronTriangularRectangleIntegrand (perronLowerPoint x)
              U M N K L χ ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        (∫ t : ℝ,
          perronTriangularRectangleIntegrand (perronUpperPoint x)
            U M N K L χ ((1 : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t : ℝ,
          perronTriangularRectangleIntegrand (perronLowerPoint x)
            U M N K L χ ((1 : ℂ) + (t : ℂ) * Complex.I) :=
    MeasureTheory.integral_sub
      (integrable_perronTriangularRectangleIntegrand
        (perronUpperPoint_pos x) U M N K L χ)
      (integrable_perronTriangularRectangleIntegrand
        (perronLowerPoint_pos hx) U M N K L χ)
  rw [hsub]
  ring

/-- Summing the exact sharp Perron representation over all dyadic boundary
rectangles leaves no sharp-to-smooth remainder. -/
theorem sharpTypeIIBoundarySumMean_le_perronMajorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIBoundarySum x U V i.2‖) ≤
            ∑ p ∈ typeIIBoundaryPairs x U V,
              (1 / (2 * Real.pi)) *
                Real.sqrt
                  (typeIISpectralRectangleMajorant C₀ C₁ D Q
                    (2 ^ p.1 * U) (2 ^ p.1 * U)
                    (2 ^ p.2 * V) (2 ^ p.2 * V)) *
                (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                  2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                    (x : ℝ)) := by
  rcases perronSharpVerticalIntegralMean_le_explicit with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hU hV hD hDQ
  let P := typeIIBoundaryPairs x U V
  let J := characterIndicesIoc D Q
  let R : (k : ℕ) × DirichletCharacter ℂ k → ℕ × ℕ → ℂ :=
    fun χ p => sharpTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ.2
  have hnorm (χ : (k : ℕ) × DirichletCharacter ℂ k) :
      ‖∑ p ∈ P, R χ p‖ ≤ ∑ p ∈ P, ‖R χ p‖ := norm_sum_le _ _
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖sharpTypeIIBoundarySum x U V i.2‖) =
        ∑ i ∈ J, primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖ by rfl]
  calc
    (∑ i ∈ J, primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖) ≤
        ∑ i ∈ J, ∑ p ∈ P,
          primitiveDyadicWeight i * ‖R i p‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖ ≤
            primitiveDyadicWeight i * ∑ p ∈ P, ‖R i p‖ :=
          mul_le_mul_of_nonneg_left (hnorm i) (primitiveDyadicWeight_nonneg i)
        _ = ∑ p ∈ P, primitiveDyadicWeight i * ‖R i p‖ := by
          simp only [Finset.mul_sum]
    _ = ∑ p ∈ P, ∑ i ∈ J,
          primitiveDyadicWeight i * ‖R i p‖ := by rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ P,
        (1 / (2 * Real.pi)) *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q
              (2 ^ p.1 * U) (2 ^ p.1 * U)
              (2 ^ p.2 * V) (2 ^ p.2 * V)) *
          (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
            2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
              (x : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hUp : 1 ≤ 2 ^ p.1 * U := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      have hVp : 1 ≤ 2 ^ p.2 * V := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      have hrect := hrectangle x U D Q
        (2 ^ p.1 * U) (2 ^ p.1 * U)
        (2 ^ p.2 * V) (2 ^ p.2 * V) (x : ℝ)
        (by omega) (by exact_mod_cast (show 0 < x by omega))
        hD hDQ hUp hVp (by omega) (by omega)
      calc
        (∑ i ∈ J, primitiveDyadicWeight i * ‖R i p‖) =
            ∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖VerticalIntegral'
                    (perronSharpRectangleIntegrand x U
                      (2 ^ p.1 * U) (2 ^ p.1 * U)
                      (2 ^ p.2 * V) (2 ^ p.2 * V) i.2) 1‖ := by
          dsimp only [J]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only [R]
          rw [sharpTypeIIRectangle_eq_perronVerticalIntegral x U
            (2 ^ p.1 * U) (2 ^ p.1 * U)
            (2 ^ p.2 * V) (2 ^ p.2 * V) i.2 (by omega)]
        _ ≤ _ := hrect

/-- Uniform sharp-boundary estimate after absorbing every dyadic rectangle
into the common conductor scale.  Unlike the older smoothed decomposition,
this estimate has no separately unbounded boundary remainder. -/
theorem sharpTypeIIBoundarySumMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIBoundarySum x U V i.2‖) ≤
            ((typeIIBoundaryPairs x U V).card : ℝ) *
              ((1 / (2 * Real.pi)) *
                Real.sqrt
                  (2 * C₀ ^ 2 * C₁ *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) *
                (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                  2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                    (x : ℝ))) := by
  rcases sharpTypeIIBoundarySumMean_le_perronMajorants with
    ⟨C₀, C₁, hC₀, hC₁, hboundary⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hU hV hD hDQ
  let K : ℝ :=
    (1 / (2 * Real.pi)) *
      Real.sqrt
        (2 * C₀ ^ 2 * C₁ *
          typeIIBoundaryConductorScale D Q U V x *
          Real.log (2 * (x : ℝ)) ^ 5) *
      (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (x : ℝ))
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖sharpTypeIIBoundarySum x U V i.2‖) ≤
        ∑ p ∈ typeIIBoundaryPairs x U V,
          (1 / (2 * Real.pi)) *
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q
                (2 ^ p.1 * U) (2 ^ p.1 * U)
                (2 ^ p.2 * V) (2 ^ p.2 * V)) *
            (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
              2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                (x : ℝ)) :=
      hboundary x U V D Q hx hU hV hD hDQ
    _ ≤ ∑ _p ∈ typeIIBoundaryPairs x U V, K := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [K]
      have hmajorant := typeIISpectralRectangleMajorant_boundary_le
        C₀ C₁ D Q hC₁.le hD hU hV hp
      have hmass :
          0 ≤ 4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
            2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
              (x : ℝ) := by
        have hlog : 0 ≤ Real.log (1 + (x : ℝ)) :=
          Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ 1 + x by omega))
        apply add_nonneg
        · exact mul_nonneg (mul_nonneg (by norm_num)
            (by unfold perronUpperPoint; positivity)) hlog
        · exact div_nonneg
            (mul_nonneg (by norm_num)
              (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmajorant)
          (by positivity)) hmass
    _ = ((typeIIBoundaryPairs x U V).card : ℝ) * K := by simp
    _ = ((typeIIBoundaryPairs x U V).card : ℝ) *
        ((1 / (2 * Real.pi)) *
          Real.sqrt
            (2 * C₀ ^ 2 * C₁ *
              typeIIBoundaryConductorScale D Q U V x *
              Real.log (2 * (x : ℝ)) ^ 5) *
          (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
            2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
              (x : ℝ))) := rfl

end Chen.BombieriVinogradov
