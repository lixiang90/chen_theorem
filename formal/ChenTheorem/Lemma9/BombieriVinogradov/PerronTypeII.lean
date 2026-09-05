import ChenTheorem.Lemma9.BombieriVinogradov.DyadicTypeII
import PrimeNumberTheoremAnd.PerronFormula

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# An exact Perron replacement for the Type-II boundary

The absolutely convergent Perron kernel `1 / (s * (s + 1))` represents the
triangular cutoff `(1 - n / X)₊`.  Taking the difference at the two
half-integers `x + 1/2` and `x - 1/2` recovers the sharp cutoff at every
integer, apart from an explicit half-weight on `n = x`.  Combining the two
Perron integrands before taking norms retains the cancellation which removes
the otherwise fatal extra factor of `x`.
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

/-- The two half-integer locations used to recover the sharp integer
cutoff from triangular weights. -/
noncomputable def perronUpperPoint (x : ℕ) : ℝ := (x : ℝ) + 1 / 2

noncomputable def perronLowerPoint (x : ℕ) : ℝ := (x : ℝ) - 1 / 2

theorem perronLowerPoint_pos {x : ℕ} (hx : 1 ≤ x) :
    0 < perronLowerPoint x := by
  unfold perronLowerPoint
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  linarith

theorem perronUpperPoint_pos (x : ℕ) :
    0 < perronUpperPoint x := by
  unfold perronUpperPoint
  positivity

theorem natCast_ne_perronUpperPoint (x n : ℕ) :
    (n : ℝ) ≠ perronUpperPoint x := by
  unfold perronUpperPoint
  by_cases hnx : n ≤ x
  · have hcast : (n : ℝ) ≤ x := by exact_mod_cast hnx
    linarith
  · have hcast : (x : ℝ) + 1 ≤ n := by
      exact_mod_cast (show x + 1 ≤ n by omega)
    linarith

theorem natCast_ne_perronLowerPoint (x n : ℕ) :
    (n : ℝ) ≠ perronLowerPoint x := by
  unfold perronLowerPoint
  by_cases hnx : n < x
  · have hcast : (n : ℝ) + 1 ≤ x := by
      exact_mod_cast (show n + 1 ≤ x by omega)
    linarith
  · have hcast : (x : ℝ) ≤ n := by
      exact_mod_cast (show x ≤ n by omega)
    linarith

/-- The explicit half-weight supported on the integer boundary `n = x`. -/
noncomputable def perronBoundaryHalfWeight (x n : ℕ) : ℝ :=
  if n = x then 1 / 2 else 0

/-- Exact recovery of the sharp cutoff on the integer lattice. -/
theorem sharpIndicator_eq_perronTriangularDifference
    (x n : ℕ) (hx : 1 ≤ x) :
    (if n ≤ x then (1 : ℝ) else 0) =
      perronUpperPoint x *
          perronTriangularWeight (perronUpperPoint x) n -
        perronLowerPoint x *
          perronTriangularWeight (perronLowerPoint x) n +
        perronBoundaryHalfWeight x n := by
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
    simp only [perronTriangularWeight, if_pos hnu, if_pos hnl,
      perronBoundaryHalfWeight, if_neg hnlt.ne]
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
        linarith
      simp only [le_rfl, ↓reduceIte, perronTriangularWeight, hxu, hxl,
        perronBoundaryHalfWeight]
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
      simp [hnle, perronTriangularWeight, hnu, hnl,
        perronBoundaryHalfWeight, hne]

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
Perron vertical integral.  The nonintegrality hypothesis is automatic for
the two half-integer points used below. -/
theorem perronTriangularTypeIIRectangle_eq_verticalIntegral
    {q : ℕ} {X : ℝ} (hX : 0 < X)
    (hXnotNat : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≠ X)
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
      simpa only [Nat.cast_mul] using
        perronTriangularWeight_eq_verticalIntegral hX hlm
          (hXnotNat (l * m) hlm)
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
    (fun n _hn => natCast_ne_perronUpperPoint x n)
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
    (fun n _hn => natCast_ne_perronLowerPoint x n)
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

/-- The part of a Type-II rectangle lying exactly on `l*m=x`. -/
noncomputable def typeIIEqualityRectangle {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc M (M + N),
    ∑ m ∈ Finset.Ioc K (K + L),
      if l * m = x then
        (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)
      else 0

/-- Exact rectangle-level recovery of the sharp cutoff from two triangular
cutoffs and the explicit integer-boundary half-weight. -/
theorem sharpTypeIIRectangle_eq_perronDifference_add_boundary
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    sharpTypeIIRectangle x U M N K L χ =
      perronTriangularTypeIIRectangle (perronUpperPoint x)
          U M N K L χ -
        perronTriangularTypeIIRectangle (perronLowerPoint x)
          U M N K L χ +
        (1 / 2 : ℝ) • typeIIEqualityRectangle x U M N K L χ := by
  rw [sharpTypeIIRectangle, perronTriangularTypeIIRectangle,
    perronTriangularTypeIIRectangle, typeIIEqualityRectangle]
  simp_rw [sharpTypeIITerm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.smul_sum]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
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
  have hboundary :
      (1 / 2 : ℝ) • (if l * m = x then B else 0) =
        B * (perronBoundaryHalfWeight x (l * m) : ℂ) := by
    by_cases heq : l * m = x
    · simp [heq, perronBoundaryHalfWeight, Complex.real_smul]
      ring
    · simp [heq, perronBoundaryHalfWeight]
  have hindC := congrArg (fun r : ℝ => (r : ℂ)) hind
  push_cast at hindC
  change (if l * m ≤ x then B else 0) = _
  rw [hleft, hboundary, hindC]
  dsimp only [B]
  push_cast
  ring

/-- Exact cancellation-preserving Perron representation of a sharp Type-II
rectangle, up to the explicit half-weight on the integer boundary. -/
theorem sharpTypeIIRectangle_eq_perronVerticalIntegral_add_boundary
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 1 ≤ x) :
    sharpTypeIIRectangle x U M N K L χ =
      VerticalIntegral'
          (perronSharpRectangleIntegrand x U M N K L χ) 1 +
        (1 / 2 : ℝ) • typeIIEqualityRectangle x U M N K L χ := by
  rw [sharpTypeIIRectangle_eq_perronDifference_add_boundary
      x U M N K L χ hx,
    perronUpperTypeIIRectangle_eq_verticalIntegral x U M N K L χ,
    perronLowerTypeIIRectangle_eq_verticalIntegral x U M N K L χ hx]
  congr 1
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

end Chen.BombieriVinogradov
