import ChenTheorem.Lemma9.BombieriVinogradov.MellinTypeII

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Dyadic assembly of the Type-II hyperbola

The Mellin estimate is rectangular.  This file supplies the exact finite
dyadic cover needed to reconstruct the two long variables of Vaughan's
Type-II term without replacing the hyperbola by a staircase.
-/

/-- A number of dyadic scales sufficient for every interval `(H,x]` with
positive `H`. -/
def typeIIDyadicIndices (x : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 x + 1)

/-- The `i`-th doubling interval above a positive starting point `H`. -/
def typeIIDyadicBlock (H i : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ i * H) (2 ^ (i + 1) * H)

theorem typeIIDyadicBlock_eq_Ioc_add (H i : ℕ) :
    typeIIDyadicBlock H i =
      Finset.Ioc (2 ^ i * H) (2 ^ i * H + 2 ^ i * H) := by
  unfold typeIIDyadicBlock
  congr 1
  rw [pow_succ]
  ring

theorem typeIIDyadicBlocks_pairwiseDisjoint (x H : ℕ) :
    Set.PairwiseDisjoint (typeIIDyadicIndices x) (typeIIDyadicBlock H) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  rw [typeIIDyadicBlock, Finset.mem_Ioc] at hni hnj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega

/-- Every integer in `(H,x]` occurs in one of the selected doubling
intervals.  The blocks are allowed to extend past `x`; later summands vanish
there because of the smooth cutoff. -/
theorem Ioc_subset_typeIIDyadicBlocks
    {x H : ℕ} (hH : 1 ≤ H) :
    Finset.Ioc H x ⊆
      (typeIIDyadicIndices x).biUnion (typeIIDyadicBlock H) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_biUnion]
  refine ⟨Nat.log 2 ((n - 1) / H), ?_, ?_⟩
  · rw [typeIIDyadicIndices, Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.log_mono_right
    exact (Nat.div_le_self (n - 1) H).trans (by omega)
  · rw [typeIIDyadicBlock, Finset.mem_Ioc]
    constructor
    · have hr : 0 < (n - 1) / H := Nat.div_pos (by omega) (by omega)
      have hp := Nat.pow_log_le_self 2 hr.ne'
      have hmul : 2 ^ Nat.log 2 ((n - 1) / H) * H ≤ n - 1 := by
        calc
          2 ^ Nat.log 2 ((n - 1) / H) * H ≤
              ((n - 1) / H) * H := Nat.mul_le_mul_right H hp
          _ ≤ n - 1 := Nat.div_mul_le_self _ _
      omega
    · have hp : (n - 1) / H <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
      have hmul : n - 1 <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) * H :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < H)).mp hp
      omega

/-- Exact reconstruction of a finite interval from the extended dyadic
blocks for a function whose tail past `x` vanishes. -/
theorem sum_Ioc_eq_sum_typeIIDyadicBlocks
    {R : Type*} [AddCommMonoid R]
    {x H : ℕ} (hH : 1 ≤ H) (f : ℕ → R)
    (hzero : ∀ n, x < n → f n = 0) :
    (∑ n ∈ Finset.Ioc H x, f n) =
      ∑ i ∈ typeIIDyadicIndices x,
        ∑ n ∈ typeIIDyadicBlock H i, f n := by
  let U := (typeIIDyadicIndices x).biUnion (typeIIDyadicBlock H)
  have hsubset : Finset.Ioc H x ⊆ U := by
    simpa only [U] using Ioc_subset_typeIIDyadicBlocks hH
  calc
    (∑ n ∈ Finset.Ioc H x, f n) = ∑ n ∈ U, f n := by
      apply Finset.sum_subset hsubset
      intro n hnU hnNot
      have hnH : H < n := by
        change n ∈ (typeIIDyadicIndices x).biUnion
          (typeIIDyadicBlock H) at hnU
        rw [Finset.mem_biUnion] at hnU
        obtain ⟨i, _hi, hni⟩ := hnU
        rw [typeIIDyadicBlock, Finset.mem_Ioc] at hni
        have hbase : H ≤ 2 ^ i * H := by
          have hone : 1 ≤ (2 : ℕ) ^ i := one_le_pow₀ (by norm_num)
          simpa only [one_mul] using Nat.mul_le_mul_right H hone
        omega
      have hnx : x < n := by
        by_contra h
        exact hnNot (Finset.mem_Ioc.mpr ⟨hnH, le_of_not_gt h⟩)
      exact hzero n hnx
    _ = ∑ i ∈ typeIIDyadicIndices x,
          ∑ n ∈ typeIIDyadicBlock H i, f n :=
      Finset.sum_biUnion (typeIIDyadicBlocks_pairwiseDisjoint x H)

/-- A single smoothly truncated visible Type-II summand. -/
noncomputable def smoothedTypeIITerm {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) (l m : ℕ) : ℂ :=
  (vaughanTypeIILeftCoefficient U l : ℂ) *
    (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
      (Chen.chenPhi (x : ℝ) ((x : ℝ) / ((l : ℝ) * m)) : ℂ)

/-- The complete visible Type-II sum with Chen's smooth product cutoff. -/
noncomputable def smoothedTypeIISum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc U x,
    ∑ m ∈ Finset.Ioc V x, smoothedTypeIITerm x U χ l m

/-- A single term of the original sharply truncated visible Type-II sum.
This is kept separate from `smoothedTypeIITerm`: rectangles wholly below
the hyperbola can be estimated directly by the bilinear large sieve, without
paying the Mellin factor `x / (l*m)`. -/
noncomputable def sharpTypeIITerm {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) (l m : ℕ) : ℂ :=
  if l * m ≤ x then
    (vaughanTypeIILeftCoefficient U l : ℂ) *
      (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)
  else 0

/-- The visible Type-II double sum with the exact hyperbola cutoff. -/
noncomputable def sharpTypeIISum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc U x,
    ∑ m ∈ Finset.Ioc V x, sharpTypeIITerm x U χ l m

/-- A sharp Type-II rectangle.  On rectangles whose upper-right corner lies
below `l*m = x`, this is an ordinary separable bilinear character sum. -/
noncomputable def sharpTypeIIRectangle {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc M (M + N),
    ∑ m ∈ Finset.Ioc K (K + L), sharpTypeIITerm x U χ l m

/-- The sharp double sum is exactly Vaughan's visible Type-II term. -/
theorem vaughanTypeIISum_eq_sharpTypeIISum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ = sharpTypeIISum x U V χ := by
  rw [vaughanTypeIISum_eq_visible_hyperbola, sharpTypeIISum]
  apply Finset.sum_congr rfl
  intro l hl
  have hlpos : 0 < l := by
    have := (Finset.mem_Ioc.mp hl).1
    omega
  have hinterval :
      Finset.Ioc V (x / l) =
        (Finset.Ioc V x).filter (fun m => l * m ≤ x) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · intro hm
      have hprod : l * m ≤ x := by
        simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hlpos).mp hm.2
      have hmle : m ≤ x := by
        have hmlm : m ≤ l * m := by nlinarith
        exact hmlm.trans hprod
      exact ⟨⟨hm.1, hmle⟩, hprod⟩
    · intro hm
      exact ⟨hm.1.1, (Nat.le_div_iff_mul_le hlpos).mpr (by
        simpa [Nat.mul_comm] using hm.2)⟩
  rw [hinterval, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hprod : l * m ≤ x
  · simp only [hprod, ↓reduceIte, sharpTypeIITerm]
    rw [map_mul]
    ring
  · simp [hprod, sharpTypeIITerm]

theorem sharpTypeIITerm_eq_zero_of_left_gt {q x U l m : ℕ}
    {χ : DirichletCharacter ℂ q}
    (hm : 1 ≤ m) (hl : x < l) :
    sharpTypeIITerm x U χ l m = 0 := by
  rw [sharpTypeIITerm, if_neg]
  nlinarith

theorem sharpTypeIITerm_eq_zero_of_right_gt {q x U l m : ℕ}
    {χ : DirichletCharacter ℂ q}
    (hl : 1 ≤ l) (hm : x < m) :
    sharpTypeIITerm x U χ l m = 0 := by
  rw [sharpTypeIITerm, if_neg]
  nlinarith

theorem sharpTypeIIRectangle_eq_zero_of_lower_product_ge
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hprod : x ≤ M * K) :
    sharpTypeIIRectangle x U M N K L χ = 0 := by
  rw [sharpTypeIIRectangle]
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  rw [sharpTypeIITerm, if_neg]
  have hldata := Finset.mem_Ioc.mp hl
  have hmdata := Finset.mem_Ioc.mp hm
  nlinarith

theorem smoothedTypeIITerm_eq_zero_of_left_gt {q x U l m : ℕ}
    {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hm : 1 ≤ m) (hl : x < l) :
    smoothedTypeIITerm x U χ l m = 0 := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlpos : 0 < l := by omega
  have hmpos : 0 < m := by omega
  have hden : 0 < (l : ℝ) * m := by positivity
  have hnat : x ≤ l * m := by
    have : l ≤ l * m := by nlinarith
    omega
  have hquot : (x : ℝ) / ((l : ℝ) * m) ≤ 1 :=
    (div_le_one hden).2 (by exact_mod_cast hnat)
  rw [smoothedTypeIITerm,
    Chen.chenPhi_eq_zero hxreal (by positivity) hquot]
  simp

theorem smoothedTypeIITerm_eq_zero_of_right_gt {q x U l m : ℕ}
    {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hl : 1 ≤ l) (hm : x < m) :
    smoothedTypeIITerm x U χ l m = 0 := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlpos : 0 < l := by omega
  have hmpos : 0 < m := by omega
  have hden : 0 < (l : ℝ) * m := by positivity
  have hnat : x ≤ l * m := by
    have : m ≤ l * m := by nlinarith
    omega
  have hquot : (x : ℝ) / ((l : ℝ) * m) ≤ 1 :=
    (div_le_one hden).2 (by exact_mod_cast hnat)
  rw [smoothedTypeIITerm,
    Chen.chenPhi_eq_zero hxreal (by positivity) hquot]
  simp

theorem smoothedTypeIITerm_eq_zero_of_product_ge {q x U l m : ℕ}
    {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hl : 1 ≤ l) (hm : 1 ≤ m) (hprod : x ≤ l * m) :
    smoothedTypeIITerm x U χ l m = 0 := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hden : 0 < (l : ℝ) * m := by positivity
  have hquot : (x : ℝ) / ((l : ℝ) * m) ≤ 1 :=
    (div_le_one hden).2 (by exact_mod_cast hprod)
  rw [smoothedTypeIITerm,
    Chen.chenPhi_eq_zero hxreal (by positivity) hquot]
  simp

/-- Exact pointwise shape of the sharp-to-smooth correction below the
hyperbola. -/
theorem sharpTypeIITerm_sub_smoothedTypeIITerm_of_product_le
    {q x U l m : ℕ} {χ : DirichletCharacter ℂ q}
    (hprod : l * m ≤ x) :
    sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m =
      ((vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)) *
        (1 - (Chen.chenPhi (x : ℝ)
          ((x : ℝ) / ((l : ℝ) * m)) : ℂ)) := by
  rw [sharpTypeIITerm, if_pos hprod, smoothedTypeIITerm]
  ring

/-- Above the hyperbola both the sharp and smooth summands vanish. -/
theorem sharpTypeIITerm_sub_smoothedTypeIITerm_of_product_gt
    {q x U l m : ℕ} {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hl : 1 ≤ l) (hm : 1 ≤ m) (hprod : x < l * m) :
    sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m = 0 := by
  rw [sharpTypeIITerm, if_neg (Nat.not_le.mpr hprod)]
  rw [smoothedTypeIITerm_eq_zero_of_product_ge hx hl hm hprod.le]
  simp

/-- Below the hyperbola, the norm of the correction is controlled solely by
the scalar smoothing defect `1 - Φ`. -/
theorem norm_sharpTypeIITerm_sub_smoothedTypeIITerm_le
    {q x U l m : ℕ} {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hl : 1 ≤ l) (hm : 1 ≤ m) (hprod : l * m ≤ x) :
    ‖sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m‖ ≤
      |vaughanTypeIILeftCoefficient U l| *
        ArithmeticFunction.vonMangoldt m *
          (1 - Chen.chenPhi (x : ℝ) ((x : ℝ) / ((l : ℝ) * m))) := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hquot : 0 ≤ (x : ℝ) / ((l : ℝ) * m) := by positivity
  have hphi0 := Chen.chenPhi_nonneg (x : ℝ) hxreal hquot
  have hphi1 := Chen.chenPhi_le_one (x : ℝ) hxreal hquot
  have hdefect : 0 ≤
      1 - Chen.chenPhi (x : ℝ) ((x : ℝ) / ((l : ℝ) * m)) := by linarith
  rw [sharpTypeIITerm_sub_smoothedTypeIITerm_of_product_le hprod,
    norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hdefectNorm :
      ‖(1 - (Chen.chenPhi (x : ℝ)
          ((x : ℝ) / ((l : ℝ) * m)) : ℂ))‖ =
        1 - Chen.chenPhi (x : ℝ) ((x : ℝ) / ((l : ℝ) * m)) := by
    rw [show (1 - (Chen.chenPhi (x : ℝ)
          ((x : ℝ) / ((l : ℝ) * m)) : ℂ)) =
        ((1 - Chen.chenPhi (x : ℝ)
          ((x : ℝ) / ((l : ℝ) * m)) : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdefect]
  rw [hdefectNorm]
  have hbase :
      |vaughanTypeIILeftCoefficient U l| *
          ArithmeticFunction.vonMangoldt m * ‖χ (l * m)‖ ≤
        |vaughanTypeIILeftCoefficient U l| *
          ArithmeticFunction.vonMangoldt m := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left
        (DirichletCharacter.norm_le_one χ (l * m))
        (show 0 ≤ |vaughanTypeIILeftCoefficient U l| *
            ArithmeticFunction.vonMangoldt m by positivity)
  exact mul_le_mul_of_nonneg_right hbase hdefect

/-- Away from the narrow transition strip, Lemma 1 supplies the power-saving
`x⁻¹/¹⁰` pointwise correction. -/
theorem norm_sharpTypeIITerm_sub_smoothedTypeIITerm_le_rpow
    {q x U l m : ℕ} {χ : DirichletCharacter ℂ q}
    (hx : 2 ≤ x) (hxlog : (10 : ℝ) ^ 4 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hm : 1 ≤ m) (hprod : l * m ≤ x)
    (hdeep : Real.exp (2 * (Real.log (x : ℝ)) ^ (-(0.1 : ℝ))) ≤
      (x : ℝ) / ((l : ℝ) * m)) :
    ‖sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m‖ ≤
      |vaughanTypeIILeftCoefficient U l| *
        ArithmeticFunction.vonMangoldt m * (x : ℝ) ^ (-(0.1 : ℝ)) := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hquot : 0 ≤ (x : ℝ) / ((l : ℝ) * m) := by positivity
  have hphi := Chen.chenPhi_ge hxreal hxlog hdeep
  calc
    ‖sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m‖ ≤
        |vaughanTypeIILeftCoefficient U l| *
          ArithmeticFunction.vonMangoldt m *
            (1 - Chen.chenPhi (x : ℝ)
              ((x : ℝ) / ((l : ℝ) * m))) :=
      norm_sharpTypeIITerm_sub_smoothedTypeIITerm_le
        hx hl hm hprod
    _ ≤ |vaughanTypeIILeftCoefficient U l| *
          ArithmeticFunction.vonMangoldt m * (x : ℝ) ^ (-(0.1 : ℝ)) := by
      gcongr
      linarith

theorem smoothedTypeIIRectangle_eq_zero_of_lower_product_ge
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hprod : x ≤ M * K) :
    smoothedTypeIIRectangle x U M N K L χ = 0 := by
  rw [smoothedTypeIIRectangle]
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  have hldata := Finset.mem_Ioc.mp hl
  have hmdata := Finset.mem_Ioc.mp hm
  apply smoothedTypeIITerm_eq_zero_of_product_ge hx (by omega) (by omega)
  exact hprod.trans (Nat.mul_le_mul (Nat.le_of_lt hldata.1)
    (Nat.le_of_lt hmdata.1))

/-- A rectangle correction is the sum of its pointwise corrections. -/
theorem sharpTypeIIRectangle_sub_smoothedTypeIIRectangle
    {q : ℕ} (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) :
    sharpTypeIIRectangle x U M N K L χ -
        smoothedTypeIIRectangle x U M N K L χ =
      ∑ l ∈ Finset.Ioc M (M + N),
        ∑ m ∈ Finset.Ioc K (K + L),
          (sharpTypeIITerm x U χ l m - smoothedTypeIITerm x U χ l m) := by
  rw [sharpTypeIIRectangle, smoothedTypeIIRectangle,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rfl

/-- Exact dyadic rectangle decomposition of the complete smoothed Type-II
sum.  The rectangles may extend beyond `x`; the smooth product cutoff makes
all such extra terms identically zero. -/
theorem smoothedTypeIISum_eq_sum_dyadicRectangles {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    smoothedTypeIISum x U V χ =
      ∑ i ∈ typeIIDyadicIndices x,
        ∑ j ∈ typeIIDyadicIndices x,
          smoothedTypeIIRectangle x U
            (2 ^ i * U) (2 ^ i * U)
            (2 ^ j * V) (2 ^ j * V) χ := by
  rw [smoothedTypeIISum]
  calc
    (∑ l ∈ Finset.Ioc U x,
        ∑ m ∈ Finset.Ioc V x, smoothedTypeIITerm x U χ l m) =
        ∑ i ∈ typeIIDyadicIndices x,
          ∑ l ∈ typeIIDyadicBlock U i,
            ∑ m ∈ Finset.Ioc V x, smoothedTypeIITerm x U χ l m := by
      apply sum_Ioc_eq_sum_typeIIDyadicBlocks hU
      intro l hlx
      apply Finset.sum_eq_zero
      intro m hm
      exact smoothedTypeIITerm_eq_zero_of_left_gt hx
        (by have := (Finset.mem_Ioc.mp hm).1; omega) hlx
    _ = ∑ i ∈ typeIIDyadicIndices x,
          ∑ j ∈ typeIIDyadicIndices x,
            ∑ l ∈ typeIIDyadicBlock U i,
              ∑ m ∈ typeIIDyadicBlock V j,
                smoothedTypeIITerm x U χ l m := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ l ∈ typeIIDyadicBlock U i,
            ∑ m ∈ Finset.Ioc V x, smoothedTypeIITerm x U χ l m) =
            ∑ l ∈ typeIIDyadicBlock U i,
              ∑ j ∈ typeIIDyadicIndices x,
                ∑ m ∈ typeIIDyadicBlock V j,
                  smoothedTypeIITerm x U χ l m := by
          apply Finset.sum_congr rfl
          intro l hl
          apply sum_Ioc_eq_sum_typeIIDyadicBlocks hV
          intro m hmx
          have hlblock := Finset.mem_Ioc.mp
            (show l ∈ Finset.Ioc (2 ^ i * U) (2 ^ (i + 1) * U) by
              simpa only [typeIIDyadicBlock] using hl)
          exact smoothedTypeIITerm_eq_zero_of_right_gt hx
            (by omega) hmx
        _ = ∑ j ∈ typeIIDyadicIndices x,
              ∑ l ∈ typeIIDyadicBlock U i,
                ∑ m ∈ typeIIDyadicBlock V j,
                  smoothedTypeIITerm x U χ l m := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ typeIIDyadicIndices x,
          ∑ j ∈ typeIIDyadicIndices x,
            smoothedTypeIIRectangle x U
              (2 ^ i * U) (2 ^ i * U)
              (2 ^ j * V) (2 ^ j * V) χ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [smoothedTypeIIRectangle, smoothedTypeIITerm,
        typeIIDyadicBlock_eq_Ioc_add,
        typeIIDyadicBlock_eq_Ioc_add]

/-- Exact dyadic rectangle decomposition of the sharply truncated Type-II
sum.  As above, the rectangles may extend beyond `x`; the sharp product
indicator kills every added term. -/
theorem sharpTypeIISum_eq_sum_dyadicRectangles {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    sharpTypeIISum x U V χ =
      ∑ i ∈ typeIIDyadicIndices x,
        ∑ j ∈ typeIIDyadicIndices x,
          sharpTypeIIRectangle x U
            (2 ^ i * U) (2 ^ i * U)
            (2 ^ j * V) (2 ^ j * V) χ := by
  rw [sharpTypeIISum]
  calc
    (∑ l ∈ Finset.Ioc U x,
        ∑ m ∈ Finset.Ioc V x, sharpTypeIITerm x U χ l m) =
        ∑ i ∈ typeIIDyadicIndices x,
          ∑ l ∈ typeIIDyadicBlock U i,
            ∑ m ∈ Finset.Ioc V x, sharpTypeIITerm x U χ l m := by
      apply sum_Ioc_eq_sum_typeIIDyadicBlocks hU
      intro l hlx
      apply Finset.sum_eq_zero
      intro m hm
      exact sharpTypeIITerm_eq_zero_of_left_gt
        (by have := (Finset.mem_Ioc.mp hm).1; omega) hlx
    _ = ∑ i ∈ typeIIDyadicIndices x,
          ∑ j ∈ typeIIDyadicIndices x,
            ∑ l ∈ typeIIDyadicBlock U i,
              ∑ m ∈ typeIIDyadicBlock V j,
                sharpTypeIITerm x U χ l m := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ l ∈ typeIIDyadicBlock U i,
            ∑ m ∈ Finset.Ioc V x, sharpTypeIITerm x U χ l m) =
            ∑ l ∈ typeIIDyadicBlock U i,
              ∑ j ∈ typeIIDyadicIndices x,
                ∑ m ∈ typeIIDyadicBlock V j,
                  sharpTypeIITerm x U χ l m := by
          apply Finset.sum_congr rfl
          intro l hl
          apply sum_Ioc_eq_sum_typeIIDyadicBlocks hV
          intro m hmx
          have hlblock := Finset.mem_Ioc.mp
            (show l ∈ Finset.Ioc (2 ^ i * U) (2 ^ (i + 1) * U) by
              simpa only [typeIIDyadicBlock] using hl)
          exact sharpTypeIITerm_eq_zero_of_right_gt (by omega) hmx
        _ = ∑ j ∈ typeIIDyadicIndices x,
              ∑ l ∈ typeIIDyadicBlock U i,
                ∑ m ∈ typeIIDyadicBlock V j,
                  sharpTypeIITerm x U χ l m := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ typeIIDyadicIndices x,
          ∑ j ∈ typeIIDyadicIndices x,
            sharpTypeIIRectangle x U
              (2 ^ i * U) (2 ^ i * U)
              (2 ^ j * V) (2 ^ j * V) χ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [sharpTypeIIRectangle, typeIIDyadicBlock_eq_Ioc_add]

/-- The genuinely occupied dyadic rectangle pairs below the hyperbola. -/
def typeIIDyadicPairs (x U V : ℕ) : Finset (ℕ × ℕ) :=
  ((typeIIDyadicIndices x) ×ˢ (typeIIDyadicIndices x)).filter
    (fun p => (2 ^ p.1 * U) * (2 ^ p.2 * V) < x)

theorem mem_typeIIDyadicPairs {x U V : ℕ} {p : ℕ × ℕ} :
    p ∈ typeIIDyadicPairs x U V ↔
      p.1 ∈ typeIIDyadicIndices x ∧
        p.2 ∈ typeIIDyadicIndices x ∧
          (2 ^ p.1 * U) * (2 ^ p.2 * V) < x := by
  simp [typeIIDyadicPairs, and_assoc]

/-- Occupied dyadic rectangles whose upper-right corner is still below the
sharp hyperbola.  These rectangles require no Mellin separation. -/
def typeIIInteriorPairs (x U V : ℕ) : Finset (ℕ × ℕ) :=
  (typeIIDyadicPairs x U V).filter fun p =>
    (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) ≤ x

/-- Occupied dyadic rectangles crossed by the sharp hyperbola.  On such a
rectangle the lower-left product is within a factor four of `x`, which is
exactly the condition needed to avoid the spurious Mellin loss. -/
def typeIIBoundaryPairs (x U V : ℕ) : Finset (ℕ × ℕ) :=
  (typeIIDyadicPairs x U V).filter fun p =>
    x < (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V)

/-- The sharp contribution of rectangles wholly below the hyperbola. -/
noncomputable def sharpTypeIIInteriorSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ typeIIInteriorPairs x U V,
    sharpTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ

/-- The sharp contribution of rectangles crossed by the hyperbola. -/
noncomputable def sharpTypeIIBoundarySum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ typeIIBoundaryPairs x U V,
    sharpTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ

/-- The smoothed analogue of the boundary contribution. -/
noncomputable def smoothedTypeIIBoundarySum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ typeIIBoundaryPairs x U V,
    smoothedTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ

/-- The boundary correction from the smooth cutoff back to the sharp one,
kept as a sum of local rectangle differences so its support remains visible. -/
noncomputable def typeIIBoundaryRemainderSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ typeIIBoundaryPairs x U V,
    (sharpTypeIIRectangle x U
        (2 ^ p.1 * U) (2 ^ p.1 * U)
        (2 ^ p.2 * V) (2 ^ p.2 * V) χ -
      smoothedTypeIIRectangle x U
        (2 ^ p.1 * U) (2 ^ p.1 * U)
        (2 ^ p.2 * V) (2 ^ p.2 * V) χ)

theorem mem_typeIIInteriorPairs {x U V : ℕ} {p : ℕ × ℕ} :
    p ∈ typeIIInteriorPairs x U V ↔
      p ∈ typeIIDyadicPairs x U V ∧
        (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) ≤ x := by
  simp [typeIIInteriorPairs]

theorem mem_typeIIBoundaryPairs {x U V : ℕ} {p : ℕ × ℕ} :
    p ∈ typeIIBoundaryPairs x U V ↔
      p ∈ typeIIDyadicPairs x U V ∧
        x < (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) := by
  simp [typeIIBoundaryPairs]

/-- Every occupied pair is uniquely classified as interior or boundary. -/
theorem sum_typeIIDyadicPairs_eq_interior_add_boundary
    {R : Type*} [AddCommMonoid R]
    (x U V : ℕ) (f : ℕ × ℕ → R) :
    (∑ p ∈ typeIIDyadicPairs x U V, f p) =
      (∑ p ∈ typeIIInteriorPairs x U V, f p) +
        ∑ p ∈ typeIIBoundaryPairs x U V, f p := by
  rw [typeIIInteriorPairs, typeIIBoundaryPairs]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hcorner :
      (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) ≤ x
  · have hnot : ¬x <
        (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) :=
      Nat.not_lt.mpr hcorner
    simp [hcorner, hnot]
  · have hcross : x <
        (2 ^ (p.1 + 1) * U) * (2 ^ (p.2 + 1) * V) :=
      Nat.lt_of_not_ge hcorner
    simp [hcorner, hcross]

theorem typeIIBoundaryPair_geometry
    {x U V : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ typeIIBoundaryPairs x U V) :
    let A := 2 ^ p.1 * U
    let B := 2 ^ p.2 * V
    A * B < x ∧ x < 4 * (A * B) := by
  rcases (mem_typeIIBoundaryPairs.mp hp) with ⟨hoccupied, hcross⟩
  have hlower := (mem_typeIIDyadicPairs.mp hoccupied).2.2
  dsimp only
  constructor
  · exact hlower
  · convert hcross using 1
    simp only [pow_succ]
    ring

theorem card_typeIIDyadicPairs_le (x U V : ℕ) :
    (typeIIDyadicPairs x U V).card ≤ (Nat.log 2 x + 1) ^ 2 := by
  calc
    (typeIIDyadicPairs x U V).card ≤
        ((typeIIDyadicIndices x) ×ˢ (typeIIDyadicIndices x)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (Nat.log 2 x + 1) ^ 2 := by
      simp [typeIIDyadicIndices, pow_two]

theorem card_typeIIInteriorPairs_le (x U V : ℕ) :
    (typeIIInteriorPairs x U V).card ≤ (Nat.log 2 x + 1) ^ 2 :=
  (Finset.card_filter_le _ _).trans (card_typeIIDyadicPairs_le x U V)

theorem card_typeIIBoundaryPairs_le (x U V : ℕ) :
    (typeIIBoundaryPairs x U V).card ≤ (Nat.log 2 x + 1) ^ 2 :=
  (Finset.card_filter_le _ _).trans (card_typeIIDyadicPairs_le x U V)

/-- Elementary hyperbolic geometry of one occupied dyadic pair. -/
theorem typeIIDyadicPair_geometry
    {x U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {p : ℕ × ℕ} (hp : p ∈ typeIIDyadicPairs x U V) :
    let A := 2 ^ p.1 * U
    let B := 2 ^ p.2 * V
    1 ≤ A ∧ 1 ≤ B ∧ A * B < x ∧ A * V < x ∧ U * B < x ∧
      A ≤ x ∧ B ≤ x := by
  have hpdata := mem_typeIIDyadicPairs.mp hp
  let A := 2 ^ p.1 * U
  let B := 2 ^ p.2 * V
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
  have hAB : A * B < x := by
    simpa only [A, B] using hpdata.2.2
  have hVB : V ≤ B := by
    dsimp only [B]
    have hone : 1 ≤ (2 : ℕ) ^ p.2 := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right V hone
  have hUA : U ≤ A := by
    dsimp only [A]
    have hone : 1 ≤ (2 : ℕ) ^ p.1 := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right U hone
  have hAV : A * V < x := (Nat.mul_le_mul_left A hVB).trans_lt hAB
  have hUB : U * B < x := (Nat.mul_le_mul_right B hUA).trans_lt hAB
  have hAx : A ≤ x := by
    have : A ≤ A * B := by nlinarith
    omega
  have hBx : B ≤ x := by
    have : B ≤ A * B := by nlinarith
    omega
  exact ⟨hA, hB, hAB, hAV, hUB, hAx, hBx⟩

/-- The conductor-and-cutoff scale left after the Mellin interval factors
have cancelled. -/
noncomputable def typeIIConductorScale
    (D Q U V : ℕ) : ℝ :=
  (Q : ℝ) ^ 2 / ((U : ℝ) * V) +
    (Q : ℝ) / ((D : ℝ) * U) +
    (Q : ℝ) / ((D : ℝ) * V) +
    1 / (D : ℝ) ^ 2

/-- The sharper scale available on a boundary rectangle.  The geometric
relation `x < 4*A*B` replaces the unacceptable `Q²/(U*V)` term by `4Q²/x`. -/
noncomputable def typeIIBoundaryConductorScale
    (D Q U V x : ℕ) : ℝ :=
  4 * (Q : ℝ) ^ 2 / (x : ℝ) +
    (Q : ℝ) / ((D : ℝ) * U) +
    (Q : ℝ) / ((D : ℝ) * V) +
    1 / (D : ℝ) ^ 2

/-- Exact algebraic normal form of the spectral majorant on a doubling
rectangle `(A,2A] × (B,2B]`. -/
theorem typeIISpectralRectangleMajorant_dyadic_eq
    (C₀ C₁ : ℝ) (D Q A B : ℕ)
    (hD : 1 ≤ D) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    typeIISpectralRectangleMajorant C₀ C₁ D Q A A B B =
      2 * C₀ ^ 2 * C₁ *
        (((Q : ℝ) + (A : ℝ) / D) *
          ((Q : ℝ) + (B : ℝ) / D) / ((A : ℝ) * B)) *
        Real.log (2 * (A : ℝ)) ^ 3 *
        Real.log (2 * (B : ℝ)) ^ 2 := by
  unfold typeIISpectralRectangleMajorant
  push_cast
  field_simp [show (D : ℝ) ≠ 0 by exact_mod_cast (show D ≠ 0 by omega),
    show (A : ℝ) ≠ 0 by exact_mod_cast (show A ≠ 0 by omega),
    show (B : ℝ) ≠ 0 by exact_mod_cast (show B ≠ 0 by omega)]
  ring_nf

theorem typeII_rectangle_ratio_eq
    (D Q A B : ℕ) (hD : 1 ≤ D) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (((Q : ℝ) + (A : ℝ) / D) *
        ((Q : ℝ) + (B : ℝ) / D) / ((A : ℝ) * B)) =
      (Q : ℝ) ^ 2 / ((A : ℝ) * B) +
        (Q : ℝ) / ((D : ℝ) * A) +
        (Q : ℝ) / ((D : ℝ) * B) +
        1 / (D : ℝ) ^ 2 := by
  field_simp [show (D : ℝ) ≠ 0 by exact_mod_cast (show D ≠ 0 by omega),
    show (A : ℝ) ≠ 0 by exact_mod_cast (show A ≠ 0 by omega),
    show (B : ℝ) ≠ 0 by exact_mod_cast (show B ≠ 0 by omega)]
  ring

/-- On a boundary pair, the Mellin rectangle ratio has the correct
Bombieri--Vinogradov scale. -/
theorem typeII_rectangle_ratio_le_boundaryConductorScale
    {x U V : ℕ} {p : ℕ × ℕ} (D Q : ℕ)
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hp : p ∈ typeIIBoundaryPairs x U V) :
    let A := 2 ^ p.1 * U
    let B := 2 ^ p.2 * V
    (((Q : ℝ) + (A : ℝ) / D) *
        ((Q : ℝ) + (B : ℝ) / D) / ((A : ℝ) * B)) ≤
      typeIIBoundaryConductorScale D Q U V x := by
  have hoccupied := (mem_typeIIBoundaryPairs.mp hp).1
  rcases typeIIDyadicPair_geometry hU hV hoccupied with
    ⟨hA, hB, hAB, _hAV, _hUB, _hAx, _hBx⟩
  rcases typeIIBoundaryPair_geometry hp with ⟨_hlower, hcross⟩
  have hUA : U ≤ 2 ^ p.1 * U := by
    simpa only [one_mul] using Nat.mul_le_mul_right U
      (show 1 ≤ 2 ^ p.1 by exact one_le_pow₀ (by norm_num))
  have hVB : V ≤ 2 ^ p.2 * V := by
    simpa only [one_mul] using Nat.mul_le_mul_right V
      (show 1 ≤ 2 ^ p.2 by exact one_le_pow₀ (by norm_num))
  let A := 2 ^ p.1 * U
  let B := 2 ^ p.2 * V
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by
      have hABpos : 0 < A * B := Nat.mul_pos hA hB
      omega)
  have hquarter : (x : ℝ) / 4 ≤ (A : ℝ) * B := by
    have hcross' : (x : ℝ) < 4 * ((A : ℝ) * B) := by
      exact_mod_cast hcross
    linarith
  have hQsq :
      (Q : ℝ) ^ 2 / ((A : ℝ) * B) ≤
        4 * (Q : ℝ) ^ 2 / (x : ℝ) := by
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg (Q : ℝ))
      (show 0 < (x : ℝ) / 4 by positivity) hquarter
    calc
      (Q : ℝ) ^ 2 / ((A : ℝ) * B) ≤
          (Q : ℝ) ^ 2 / ((x : ℝ) / 4) := hdiv
      _ = 4 * (Q : ℝ) ^ 2 / (x : ℝ) := by
        field_simp
  have hQA :
      (Q : ℝ) / ((D : ℝ) * A) ≤
        (Q : ℝ) / ((D : ℝ) * U) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg Q)
      (show 0 < (D : ℝ) * U by positivity)
    exact_mod_cast Nat.mul_le_mul_left D hUA
  have hQB :
      (Q : ℝ) / ((D : ℝ) * B) ≤
        (Q : ℝ) / ((D : ℝ) * V) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg Q)
      (show 0 < (D : ℝ) * V by positivity)
    exact_mod_cast Nat.mul_le_mul_left D hVB
  dsimp only [A, B]
  rw [typeII_rectangle_ratio_eq D Q (2 ^ p.1 * U) (2 ^ p.2 * V)
    hD hA hB]
  unfold typeIIBoundaryConductorScale
  linarith

/-- The complete spectral majorant on a boundary rectangle.  All dyadic
length dependence is absorbed into the common logarithm, while the conductor
factor has the sharp `Q²/x` scale. -/
theorem typeIISpectralRectangleMajorant_boundary_le
    (C₀ C₁ : ℝ) {x U V : ℕ} {p : ℕ × ℕ} (D Q : ℕ)
    (hC₁ : 0 ≤ C₁) (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hp : p ∈ typeIIBoundaryPairs x U V) :
    typeIISpectralRectangleMajorant C₀ C₁ D Q
        (2 ^ p.1 * U) (2 ^ p.1 * U)
        (2 ^ p.2 * V) (2 ^ p.2 * V) ≤
      2 * C₀ ^ 2 * C₁ * typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 5 := by
  have hoccupied := (mem_typeIIBoundaryPairs.mp hp).1
  rcases typeIIDyadicPair_geometry hU hV hoccupied with
    ⟨hA, hB, _hAB, _hAV, _hUB, hAx, hBx⟩
  have hratio := typeII_rectangle_ratio_le_boundaryConductorScale
    (p := p) D Q hD hU hV hp
  dsimp only at hratio
  have hlogA0 : 0 ≤ Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 ^ p.1 * U) by omega))
  have hlogB0 : 0 ≤ Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 ^ p.2 * V) by omega))
  have hlogX0 : 0 ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * x by
        have := (mem_typeIIDyadicPairs.mp hoccupied).2.2
        omega))
  have hlogA :
      Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ≤
        Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 hAx
  have hlogB :
      Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ≤
        Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 hBx
  have hscale : 0 ≤ typeIIBoundaryConductorScale D Q U V x := by
    unfold typeIIBoundaryConductorScale
    positivity
  rw [typeIISpectralRectangleMajorant_dyadic_eq C₀ C₁ D Q
    (2 ^ p.1 * U) (2 ^ p.2 * V) hD hA hB]
  calc
    2 * C₀ ^ 2 * C₁ *
          ((((Q : ℝ) + ((2 ^ p.1 * U : ℕ) : ℝ) / D) *
            ((Q : ℝ) + ((2 ^ p.2 * V : ℕ) : ℝ) / D) /
              (((2 ^ p.1 * U : ℕ) : ℝ) * (2 ^ p.2 * V : ℕ)))) *
        Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ^ 3 *
        Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ^ 2 ≤
      2 * C₀ ^ 2 * C₁ * typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ^ 3 *
        Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ^ 2 := by
      gcongr
    _ ≤ 2 * C₀ ^ 2 * C₁ * typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 3 * Real.log (2 * (x : ℝ)) ^ 2 := by
      gcongr
    _ = 2 * C₀ ^ 2 * C₁ * typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 5 := by ring

/-- Exact occupied-rectangle form of the smoothed Type-II sum. -/
theorem smoothedTypeIISum_eq_sum_dyadicPairs {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    smoothedTypeIISum x U V χ =
      ∑ p ∈ typeIIDyadicPairs x U V,
        smoothedTypeIIRectangle x U
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V) χ := by
  rw [smoothedTypeIISum_eq_sum_dyadicRectangles x U V χ hx hU hV]
  rw [typeIIDyadicPairs, Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hoccupied : (2 ^ i * U) * (2 ^ j * V) < x
  · simp [hoccupied]
  · simp only [hoccupied, ↓reduceIte]
    exact smoothedTypeIIRectangle_eq_zero_of_lower_product_ge
      x U (2 ^ i * U) (2 ^ i * U)
        (2 ^ j * V) (2 ^ j * V) χ hx
        (Nat.le_of_not_gt hoccupied)

/-- Exact occupied-rectangle form of the original sharp Type-II sum. -/
theorem sharpTypeIISum_eq_sum_dyadicPairs {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    sharpTypeIISum x U V χ =
      ∑ p ∈ typeIIDyadicPairs x U V,
        sharpTypeIIRectangle x U
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V) χ := by
  rw [sharpTypeIISum_eq_sum_dyadicRectangles x U V χ hU hV]
  rw [typeIIDyadicPairs, Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hoccupied : (2 ^ i * U) * (2 ^ j * V) < x
  · simp [hoccupied]
  · simp only [hoccupied, ↓reduceIte]
    exact sharpTypeIIRectangle_eq_zero_of_lower_product_ge
      x U (2 ^ i * U) (2 ^ i * U)
        (2 ^ j * V) (2 ^ j * V) χ
        (Nat.le_of_not_gt hoccupied)

/-- The sharp Type-II sum split into rectangles wholly below the hyperbola
and the boundary rectangles crossed by it. -/
theorem sharpTypeIISum_eq_sum_interior_add_boundary {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    sharpTypeIISum x U V χ =
      (∑ p ∈ typeIIInteriorPairs x U V,
        sharpTypeIIRectangle x U
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V) χ) +
      ∑ p ∈ typeIIBoundaryPairs x U V,
        sharpTypeIIRectangle x U
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V) χ := by
  rw [sharpTypeIISum_eq_sum_dyadicPairs x U V χ hU hV]
  exact sum_typeIIDyadicPairs_eq_interior_add_boundary x U V _

theorem sharpTypeIISum_eq_interior_add_boundary {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    sharpTypeIISum x U V χ =
      sharpTypeIIInteriorSum x U V χ + sharpTypeIIBoundarySum x U V χ := by
  simpa only [sharpTypeIIInteriorSum, sharpTypeIIBoundarySum] using
    sharpTypeIISum_eq_sum_interior_add_boundary x U V χ hU hV

/-- Exact sharp-to-smooth identity on the boundary family. -/
theorem sharpTypeIIBoundarySum_eq_smoothed_add_remainder {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    sharpTypeIIBoundarySum x U V χ =
      smoothedTypeIIBoundarySum x U V χ +
        typeIIBoundaryRemainderSum x U V χ := by
  unfold sharpTypeIIBoundarySum smoothedTypeIIBoundarySum
    typeIIBoundaryRemainderSum
  rw [Finset.sum_sub_distrib]
  ring

/-- Vaughan's sharp Type-II term as an interior direct contribution, a
Mellin-smoothed boundary contribution, and one explicit correction. -/
theorem vaughanTypeIISum_eq_interior_add_smoothedBoundary_add_remainder
    {q : ℕ} (x U V : ℕ) (χ : DirichletCharacter ℂ q)
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    vaughanTypeIISum x U V χ =
      sharpTypeIIInteriorSum x U V χ +
        smoothedTypeIIBoundarySum x U V χ +
          typeIIBoundaryRemainderSum x U V χ := by
  rw [vaughanTypeIISum_eq_sharpTypeIISum,
    sharpTypeIISum_eq_interior_add_boundary x U V χ hU hV,
    sharpTypeIIBoundarySum_eq_smoothed_add_remainder]
  ring

/-- On a rectangle whose upper-right corner lies below the hyperbola, the
sharp indicator is identically one and the sum separates exactly. -/
theorem sharpTypeIIRectangle_eq_mul_of_upperProduct_le {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hupper : (M + N) * (K + L) ≤ x) :
    sharpTypeIIRectangle x U M N K L χ =
      characterIntervalSum M N
          (fun n => (vaughanTypeIILeftCoefficient U n : ℂ)) χ *
        characterIntervalSum K L
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) χ := by
  rw [sharpTypeIIRectangle, characterIntervalSum, characterIntervalSum]
  calc
    (∑ l ∈ Finset.Ioc M (M + N),
        ∑ m ∈ Finset.Ioc K (K + L), sharpTypeIITerm x U χ l m) =
        ∑ l ∈ Finset.Ioc M (M + N),
          ∑ m ∈ Finset.Ioc K (K + L),
            ((vaughanTypeIILeftCoefficient U l : ℂ) * χ l) *
              ((ArithmeticFunction.vonMangoldt m : ℂ) * χ m) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro m hm
      have hprod : l * m ≤ x :=
        (Nat.mul_le_mul (Finset.mem_Ioc.mp hl).2
          (Finset.mem_Ioc.mp hm).2).trans hupper
      rw [sharpTypeIITerm, if_pos hprod, map_mul]
      ring
    _ = (∑ l ∈ Finset.Ioc M (M + N),
          (vaughanTypeIILeftCoefficient U l : ℂ) * χ l) *
        ∑ m ∈ Finset.Ioc K (K + L),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]

/-- The direct large-sieve majorant for one visible Type-II rectangle. -/
noncomputable def typeIIDirectRectangleMajorant
    (C₀ C₁ : ℝ) (D Q M N K L : ℕ) : ℝ :=
  (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
      (C₁ * ((M + N : ℕ) : ℝ) *
        Real.log ((M + N : ℕ) : ℝ) ^ 3)) *
    (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
      ((L : ℝ) * Real.log ((K + L : ℕ) : ℝ) ^ 2))

/-- Exact algebraic form of the direct majorant on a doubling rectangle. -/
theorem typeIIDirectRectangleMajorant_dyadic_eq
    (C₀ C₁ : ℝ) (D Q A B : ℕ) (hD : 1 ≤ D) :
    typeIIDirectRectangleMajorant C₀ C₁ D Q A A B B =
      2 * C₀ ^ 2 * C₁ * ((A : ℝ) * B) *
        (((Q : ℝ) + (A : ℝ) / D) *
          ((Q : ℝ) + (B : ℝ) / D)) *
        Real.log (2 * (A : ℝ)) ^ 3 *
        Real.log (2 * (B : ℝ)) ^ 2 := by
  unfold typeIIDirectRectangleMajorant
  push_cast
  field_simp [show (D : ℝ) ≠ 0 by
    exact_mod_cast (show D ≠ 0 by omega)]
  ring_nf

/-- The direct rectangle length factor has the same normalized conductor
scale as a boundary Mellin rectangle. -/
theorem typeII_direct_factor_le_boundaryConductorScale
    {x U V D Q A B : ℕ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hUA : U ≤ A) (hVB : V ≤ B) (hAB : A * B ≤ x) :
    ((A : ℝ) * B) *
        (((Q : ℝ) + (A : ℝ) / D) *
          ((Q : ℝ) + (B : ℝ) / D)) ≤
      (x : ℝ) ^ 2 * typeIIBoundaryConductorScale D Q U V x := by
  have hD0 : (D : ℝ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by omega)
  have hU0 : (U : ℝ) ≠ 0 := by
    exact_mod_cast (show U ≠ 0 by omega)
  have hV0 : (V : ℝ) ≠ 0 := by
    exact_mod_cast (show V ≠ 0 by omega)
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by
      have : 0 < A * B := Nat.mul_pos (by omega) (by omega)
      omega)
  have hABr : (A : ℝ) * B ≤ (x : ℝ) := by exact_mod_cast hAB
  have hsq : ((A : ℝ) * B) ^ 2 ≤ (x : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hABr 2
  have hfirst :
      (Q : ℝ) ^ 2 * ((A : ℝ) * B) ≤
        (x : ℝ) ^ 2 * (4 * (Q : ℝ) ^ 2 / (x : ℝ)) := by
    calc
      (Q : ℝ) ^ 2 * ((A : ℝ) * B) ≤
          (Q : ℝ) ^ 2 * (x : ℝ) := by gcongr
      _ ≤ 4 * (Q : ℝ) ^ 2 * (x : ℝ) := by
        nlinarith [mul_nonneg (sq_nonneg (Q : ℝ)) (Nat.cast_nonneg x)]
      _ = (x : ℝ) ^ 2 * (4 * (Q : ℝ) ^ 2 / (x : ℝ)) := by
        field_simp
  have hUquad :
      (U : ℝ) * ((A : ℝ) * (B : ℝ) ^ 2) ≤ (x : ℝ) ^ 2 := by
    calc
      (U : ℝ) * ((A : ℝ) * (B : ℝ) ^ 2) ≤
          (A : ℝ) * ((A : ℝ) * (B : ℝ) ^ 2) := by
        gcongr
      _ = ((A : ℝ) * B) ^ 2 := by ring
      _ ≤ (x : ℝ) ^ 2 := hsq
  have hVquad :
      (V : ℝ) * ((A : ℝ) ^ 2 * (B : ℝ)) ≤ (x : ℝ) ^ 2 := by
    calc
      (V : ℝ) * ((A : ℝ) ^ 2 * (B : ℝ)) ≤
          (B : ℝ) * ((A : ℝ) ^ 2 * (B : ℝ)) := by
        gcongr
      _ = ((A : ℝ) * B) ^ 2 := by ring
      _ ≤ (x : ℝ) ^ 2 := hsq
  have hUsecond :
      (A : ℝ) * (B : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 / (U : ℝ) := by
    apply (le_div_iff₀ (show (0 : ℝ) < U by positivity)).2
    nlinarith [hUquad]
  have hVsecond :
      (A : ℝ) ^ 2 * (B : ℝ) ≤ (x : ℝ) ^ 2 / (V : ℝ) := by
    apply (le_div_iff₀ (show (0 : ℝ) < V by positivity)).2
    nlinarith [hVquad]
  have hsecond :
      (Q : ℝ) * (A : ℝ) * (B : ℝ) ^ 2 / (D : ℝ) ≤
        (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * U)) := by
    have hnum := mul_le_mul_of_nonneg_left hUsecond (Nat.cast_nonneg Q)
    calc
      (Q : ℝ) * (A : ℝ) * (B : ℝ) ^ 2 / (D : ℝ) =
          ((Q : ℝ) * ((A : ℝ) * (B : ℝ) ^ 2)) / (D : ℝ) := by ring
      _ ≤ ((Q : ℝ) * ((x : ℝ) ^ 2 / (U : ℝ))) / (D : ℝ) :=
        div_le_div_of_nonneg_right hnum (Nat.cast_nonneg D)
      _ = (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * U)) := by
        field_simp [hD0, hU0]
  have hthird :
      (Q : ℝ) * (A : ℝ) ^ 2 * (B : ℝ) / (D : ℝ) ≤
        (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * V)) := by
    have hnum := mul_le_mul_of_nonneg_left hVsecond (Nat.cast_nonneg Q)
    calc
      (Q : ℝ) * (A : ℝ) ^ 2 * (B : ℝ) / (D : ℝ) =
          ((Q : ℝ) * ((A : ℝ) ^ 2 * (B : ℝ))) / (D : ℝ) := by ring
      _ ≤ ((Q : ℝ) * ((x : ℝ) ^ 2 / (V : ℝ))) / (D : ℝ) :=
        div_le_div_of_nonneg_right hnum (Nat.cast_nonneg D)
      _ = (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * V)) := by
        field_simp [hD0, hV0]
  have hfourth :
      ((A : ℝ) * B) ^ 2 / (D : ℝ) ^ 2 ≤
        (x : ℝ) ^ 2 * (1 / (D : ℝ) ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hsq (sq_nonneg (D : ℝ))
  unfold typeIIBoundaryConductorScale
  calc
    ((A : ℝ) * B) *
          (((Q : ℝ) + (A : ℝ) / D) *
            ((Q : ℝ) + (B : ℝ) / D)) =
        (Q : ℝ) ^ 2 * ((A : ℝ) * B) +
          (Q : ℝ) * (A : ℝ) * (B : ℝ) ^ 2 / (D : ℝ) +
          (Q : ℝ) * (A : ℝ) ^ 2 * (B : ℝ) / (D : ℝ) +
          ((A : ℝ) * B) ^ 2 / (D : ℝ) ^ 2 := by ring
    _ ≤ (x : ℝ) ^ 2 * (4 * (Q : ℝ) ^ 2 / (x : ℝ)) +
          (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * U)) +
          (x : ℝ) ^ 2 * ((Q : ℝ) / ((D : ℝ) * V)) +
          (x : ℝ) ^ 2 * (1 / (D : ℝ) ^ 2) := by gcongr
    _ = (x : ℝ) ^ 2 *
        (4 * (Q : ℝ) ^ 2 / (x : ℝ) +
          (Q : ℝ) / ((D : ℝ) * U) +
          (Q : ℝ) / ((D : ℝ) * V) +
          1 / (D : ℝ) ^ 2) := by ring

/-- A direct interior majorant, normalized to the same conductor scale as
the smoothed boundary majorant. -/
theorem typeIIDirectRectangleMajorant_interior_le
    (C₀ C₁ : ℝ) {x U V : ℕ} {p : ℕ × ℕ} (D Q : ℕ)
    (hC₁ : 0 ≤ C₁) (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hp : p ∈ typeIIInteriorPairs x U V) :
    typeIIDirectRectangleMajorant C₀ C₁ D Q
        (2 ^ p.1 * U) (2 ^ p.1 * U)
        (2 ^ p.2 * V) (2 ^ p.2 * V) ≤
      2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
        typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 5 := by
  have hoccupied := (mem_typeIIInteriorPairs.mp hp).1
  rcases typeIIDyadicPair_geometry hU hV hoccupied with
    ⟨hA, hB, hAB, _hAV, _hUB, hAx, hBx⟩
  have hUA : U ≤ 2 ^ p.1 * U := by
    simpa only [one_mul] using Nat.mul_le_mul_right U
      (show 1 ≤ 2 ^ p.1 by exact one_le_pow₀ (by norm_num))
  have hVB : V ≤ 2 ^ p.2 * V := by
    simpa only [one_mul] using Nat.mul_le_mul_right V
      (show 1 ≤ 2 ^ p.2 by exact one_le_pow₀ (by norm_num))
  have hfactor := typeII_direct_factor_le_boundaryConductorScale
    (Q := Q) hD hU hV hA hB hUA hVB hAB.le
  have hlogA0 : 0 ≤ Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 ^ p.1 * U) by omega))
  have hlogB0 : 0 ≤ Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * (2 ^ p.2 * V) by omega))
  have hlogA :
      Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ≤
        Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 hAx
  have hlogB :
      Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ≤
        Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 hBx
  have hlogX0 : 0 ≤ Real.log (2 * (x : ℝ)) :=
    hlogA0.trans hlogA
  have hscale : 0 ≤ typeIIBoundaryConductorScale D Q U V x := by
    unfold typeIIBoundaryConductorScale
    positivity
  rw [typeIIDirectRectangleMajorant_dyadic_eq C₀ C₁ D Q
    (2 ^ p.1 * U) (2 ^ p.2 * V) hD]
  calc
    2 * C₀ ^ 2 * C₁ *
          (((2 ^ p.1 * U : ℕ) : ℝ) * (2 ^ p.2 * V : ℕ)) *
          (((Q : ℝ) + ((2 ^ p.1 * U : ℕ) : ℝ) / D) *
            ((Q : ℝ) + ((2 ^ p.2 * V : ℕ) : ℝ) / D)) *
        Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ^ 3 *
        Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ^ 2 ≤
      2 * C₀ ^ 2 * C₁ *
          ((x : ℝ) ^ 2 * typeIIBoundaryConductorScale D Q U V x) *
        Real.log (2 * ((2 ^ p.1 * U : ℕ) : ℝ)) ^ 3 *
        Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ^ 2 := by
      have hmain := mul_le_mul_of_nonneg_left hfactor
        (show 0 ≤ 2 * C₀ ^ 2 * C₁ by positivity)
      have hmain' := mul_le_mul_of_nonneg_right hmain
        (pow_nonneg hlogA0 3)
      have hmain'' := mul_le_mul_of_nonneg_right hmain'
        (pow_nonneg hlogB0 2)
      simpa only [mul_assoc] using hmain''
    _ ≤ 2 * C₀ ^ 2 * C₁ *
          ((x : ℝ) ^ 2 * typeIIBoundaryConductorScale D Q U V x) *
        Real.log (2 * (x : ℝ)) ^ 3 *
        Real.log (2 * ((2 ^ p.2 * V : ℕ) : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlogB0 2)
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogA0 hlogA 3)
      positivity
    _ ≤ 2 * C₀ ^ 2 * C₁ *
          ((x : ℝ) ^ 2 * typeIIBoundaryConductorScale D Q U V x) *
        Real.log (2 * (x : ℝ)) ^ 3 * Real.log (2 * (x : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogB0 hlogB 2)
      exact mul_nonneg
        (mul_nonneg
          (show 0 ≤ 2 * C₀ ^ 2 * C₁ by positivity)
          (mul_nonneg (sq_nonneg (x : ℝ)) hscale))
        (pow_nonneg hlogX0 3)
    _ = 2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
        typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 5 := by ring

/-- Interior sharp rectangles are controlled directly, with no Mellin
factor and therefore no `x/(M*K)` loss. -/
theorem sharpTypeIIInteriorRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → 2 ≤ K + L →
          (M + N) * (K + L) ≤ x →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIRectangle x U M N K L i.2‖) ^ 2 ≤
            typeIIDirectRectangleMajorant C₀ C₁ D Q M N K L := by
  rcases vaughanTypeIIVisibleRectangleMean_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L hD hDQ hMN hKL hupper
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖sharpTypeIIRectangle x U M N K L i.2‖) =
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖characterIntervalSum M N
                (fun n => (vaughanTypeIILeftCoefficient U n : ℂ)) i.2‖ *
            ‖characterIntervalSum K L
                (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) i.2‖ by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sharpTypeIIRectangle_eq_mul_of_upperProduct_le
        x U M N K L i.2 hupper, norm_mul]
      ring]
  exact hrectangle U D Q M N K L hD hDQ hMN hKL

theorem typeIIDirectRectangleMajorant_nonneg
    {C₀ C₁ : ℝ} {D Q M N K L : ℕ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hD : 1 ≤ D) (hMN : 2 ≤ M + N) (_hKL : 2 ≤ K + L) :
    0 ≤ typeIIDirectRectangleMajorant C₀ C₁ D Q M N K L := by
  unfold typeIIDirectRectangleMajorant
  positivity

/-- Unsquared direct mean estimate for one interior rectangle. -/
theorem sharpTypeIIInteriorRectangleMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → 2 ≤ K + L →
          (M + N) * (K + L) ≤ x →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIRectangle x U M N K L i.2‖) ≤
            Real.sqrt
              (typeIIDirectRectangleMajorant C₀ C₁ D Q M N K L) := by
  rcases sharpTypeIIInteriorRectangleMean_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hsquare⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L hD hDQ hMN hKL hupper
  let S : ℝ := ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i *
      ‖sharpTypeIIRectangle x U M N K L i.2‖
  let R : ℝ := typeIIDirectRectangleMajorant C₀ C₁ D Q M N K L
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact typeIIDirectRectangleMajorant_nonneg
      hC₀.le hC₁.le hD hMN hKL
  have hsq : S ^ 2 ≤ R := by
    simpa only [S, R] using
      hsquare x U D Q M N K L hD hDQ hMN hKL hupper
  apply (sq_le_sq₀ hS (Real.sqrt_nonneg R)).1
  rw [Real.sq_sqrt hR]
  exact hsq

/-- Direct large-sieve assembly for all dyadic rectangles wholly below the
sharp hyperbola. -/
theorem sharpTypeIIInteriorSumMean_le_directMajorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIInteriorSum x U V i.2‖) ≤
            ∑ p ∈ typeIIInteriorPairs x U V,
              Real.sqrt
                (typeIIDirectRectangleMajorant C₀ C₁ D Q
                  (2 ^ p.1 * U) (2 ^ p.1 * U)
                  (2 ^ p.2 * V) (2 ^ p.2 * V)) := by
  rcases sharpTypeIIInteriorRectangleMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hU hV hD hDQ
  let P := typeIIInteriorPairs x U V
  let J := characterIndicesIoc D Q
  let R : (k : ℕ) × DirichletCharacter ℂ k → ℕ × ℕ → ℂ :=
    fun χ p => sharpTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ.2
  have hnorm (χ : (k : ℕ) × DirichletCharacter ℂ k) :
      ‖∑ p ∈ P, R χ p‖ ≤ ∑ p ∈ P, ‖R χ p‖ := norm_sum_le _ _
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖sharpTypeIIInteriorSum x U V i.2‖) =
        ∑ i ∈ J, primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖ by
      rfl]
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
          Real.sqrt
            (typeIIDirectRectangleMajorant C₀ C₁ D Q
              (2 ^ p.1 * U) (2 ^ p.1 * U)
              (2 ^ p.2 * V) (2 ^ p.2 * V)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hcorner := (mem_typeIIInteriorPairs.mp hp).2
      have hupper :
          ((2 ^ p.1 * U) + (2 ^ p.1 * U)) *
              ((2 ^ p.2 * V) + (2 ^ p.2 * V)) ≤ x := by
        convert hcorner using 1
        · simp only [pow_succ]
          ring
      have hA : 2 ≤ (2 ^ p.1 * U) + (2 ^ p.1 * U) := by
        have : 1 ≤ 2 ^ p.1 * U :=
          Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
        omega
      have hB : 2 ≤ (2 ^ p.2 * V) + (2 ^ p.2 * V) := by
        have : 1 ≤ 2 ^ p.2 * V :=
          Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
        omega
      simpa only [P, J, R] using
        hrectangle x U D Q
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V)
          hD hDQ hA hB hupper

/-- Uniform interior-sum estimate, normalized to the same conductor scale as
the smoothed boundary contribution. -/
theorem sharpTypeIIInteriorSumMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖sharpTypeIIInteriorSum x U V i.2‖) ≤
            ((typeIIInteriorPairs x U V).card : ℝ) *
              Real.sqrt
                (2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
                  typeIIBoundaryConductorScale D Q U V x *
                  Real.log (2 * (x : ℝ)) ^ 5) := by
  rcases sharpTypeIIInteriorSumMean_le_directMajorants with
    ⟨C₀, C₁, hC₀, hC₁, hinterior⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hU hV hD hDQ
  let K : ℝ :=
    Real.sqrt
      (2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
        typeIIBoundaryConductorScale D Q U V x *
        Real.log (2 * (x : ℝ)) ^ 5)
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖sharpTypeIIInteriorSum x U V i.2‖) ≤
        ∑ p ∈ typeIIInteriorPairs x U V,
          Real.sqrt
            (typeIIDirectRectangleMajorant C₀ C₁ D Q
              (2 ^ p.1 * U) (2 ^ p.1 * U)
              (2 ^ p.2 * V) (2 ^ p.2 * V)) :=
      hinterior x U V D Q hU hV hD hDQ
    _ ≤ ∑ _p ∈ typeIIInteriorPairs x U V, K := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [K]
      exact Real.sqrt_le_sqrt
        (typeIIDirectRectangleMajorant_interior_le
          C₀ C₁ D Q hC₁.le hD hU hV hp)
    _ = ((typeIIInteriorPairs x U V).card : ℝ) * K := by simp
    _ = ((typeIIInteriorPairs x U V).card : ℝ) *
        Real.sqrt
          (2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
            typeIIBoundaryConductorScale D Q U V x *
            Real.log (2 * (x : ℝ)) ^ 5) := rfl

/-- Summing the rectangular Mellin estimates gives an exact primitive-
character mean bound for the complete smoothed Type-II sum. -/
theorem smoothedTypeIISumMean_le_dyadicMajorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i * ‖smoothedTypeIISum x U V i.2‖) ≤
            ∑ a ∈ typeIIDyadicIndices x,
              ∑ b ∈ typeIIDyadicIndices x,
                (Real.exp 1 * (x : ℝ)) *
                  Real.sqrt
                    (typeIISpectralRectangleMajorant C₀ C₁ D Q
                      (2 ^ a * U) (2 ^ a * U)
                      (2 ^ b * V) (2 ^ b * V)) *
                  Real.log (x : ℝ) ^ 5 := by
  rcases smoothedTypeIIRectangleMean_le_log_five with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hxlog hU hV hD hDQ
  let I := typeIIDyadicIndices x
  let J := characterIndicesIoc D Q
  let R : (k : ℕ) × DirichletCharacter ℂ k → ℕ → ℕ → ℂ :=
    fun χ a b => smoothedTypeIIRectangle x U
      (2 ^ a * U) (2 ^ a * U)
      (2 ^ b * V) (2 ^ b * V) χ.2
  have hnorm (χ : (k : ℕ) × DirichletCharacter ℂ k) :
      ‖∑ a ∈ I, ∑ b ∈ I, R χ a b‖ ≤
        ∑ a ∈ I, ∑ b ∈ I, ‖R χ a b‖ := by
    calc
      ‖∑ a ∈ I, ∑ b ∈ I, R χ a b‖ ≤
          ∑ a ∈ I, ‖∑ b ∈ I, R χ a b‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ I, ∑ b ∈ I, ‖R χ a b‖ := by
        apply Finset.sum_le_sum
        intro a ha
        exact norm_sum_le _ _
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * ‖smoothedTypeIISum x U V i.2‖) =
        ∑ i ∈ J, primitiveDyadicWeight i *
          ‖∑ a ∈ I, ∑ b ∈ I, R i a b‖ by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smoothedTypeIISum_eq_sum_dyadicRectangles x U V i.2 hx hU hV]]
  calc
    (∑ i ∈ J, primitiveDyadicWeight i *
        ‖∑ a ∈ I, ∑ b ∈ I, R i a b‖) ≤
        ∑ i ∈ J, ∑ a ∈ I, ∑ b ∈ I,
          primitiveDyadicWeight i * ‖R i a b‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        primitiveDyadicWeight i * ‖∑ a ∈ I, ∑ b ∈ I, R i a b‖ ≤
            primitiveDyadicWeight i *
              (∑ a ∈ I, ∑ b ∈ I, ‖R i a b‖) :=
          mul_le_mul_of_nonneg_left (hnorm i) (primitiveDyadicWeight_nonneg i)
        _ = ∑ a ∈ I, ∑ b ∈ I,
              primitiveDyadicWeight i * ‖R i a b‖ := by
          simp only [Finset.mul_sum]
    _ = ∑ a ∈ I, ∑ b ∈ I, ∑ i ∈ J,
          primitiveDyadicWeight i * ‖R i a b‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ ≤ ∑ a ∈ I, ∑ b ∈ I,
          (Real.exp 1 * (x : ℝ)) *
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q
                (2 ^ a * U) (2 ^ a * U)
                (2 ^ b * V) (2 ^ b * V)) *
            Real.log (x : ℝ) ^ 5 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have hUa : 1 ≤ 2 ^ a * U := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      have hVb : 1 ≤ 2 ^ b * V := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      simpa only [I, J, R] using
        hrectangle x U D Q
          (2 ^ a * U) (2 ^ a * U)
          (2 ^ b * V) (2 ^ b * V)
          hx hxlog hD hDQ hUa hVb (by omega) (by omega)

/-- Sharpened assembly over only the dyadic pairs whose lower-left corner
lies below the hyperbola.  This is the form whose scalar majorant has the
correct order of magnitude. -/
theorem smoothedTypeIISumMean_le_occupiedMajorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i * ‖smoothedTypeIISum x U V i.2‖) ≤
            ∑ p ∈ typeIIDyadicPairs x U V,
              (Real.exp 1 * (x : ℝ)) *
                Real.sqrt
                  (typeIISpectralRectangleMajorant C₀ C₁ D Q
                    (2 ^ p.1 * U) (2 ^ p.1 * U)
                    (2 ^ p.2 * V) (2 ^ p.2 * V)) *
                Real.log (x : ℝ) ^ 5 := by
  rcases smoothedTypeIIRectangleMean_le_log_five with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hxlog hU hV hD hDQ
  let P := typeIIDyadicPairs x U V
  let J := characterIndicesIoc D Q
  let R : (k : ℕ) × DirichletCharacter ℂ k → ℕ × ℕ → ℂ :=
    fun χ p => smoothedTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ.2
  have hnorm (χ : (k : ℕ) × DirichletCharacter ℂ k) :
      ‖∑ p ∈ P, R χ p‖ ≤ ∑ p ∈ P, ‖R χ p‖ := norm_sum_le _ _
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * ‖smoothedTypeIISum x U V i.2‖) =
        ∑ i ∈ J, primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖ by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smoothedTypeIISum_eq_sum_dyadicPairs x U V i.2 hx hU hV]]
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
          (Real.exp 1 * (x : ℝ)) *
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q
                (2 ^ p.1 * U) (2 ^ p.1 * U)
                (2 ^ p.2 * V) (2 ^ p.2 * V)) *
            Real.log (x : ℝ) ^ 5 := by
      apply Finset.sum_le_sum
      intro p hp
      have hUp : 1 ≤ 2 ^ p.1 * U := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      have hVp : 1 ≤ 2 ^ p.2 * V := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      simpa only [P, J, R] using
        hrectangle x U D Q
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V)
          hx hxlog hD hDQ hUp hVp (by omega) (by omega)

/-- Mellin estimates summed only over boundary rectangles.  Unlike the
older all-occupied estimate, every majorant here benefits from
`x < 4*A*B`. -/
theorem smoothedTypeIIBoundarySumMean_le_majorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖smoothedTypeIIBoundarySum x U V i.2‖) ≤
            ∑ p ∈ typeIIBoundaryPairs x U V,
              (Real.exp 1 * (x : ℝ)) *
                Real.sqrt
                  (typeIISpectralRectangleMajorant C₀ C₁ D Q
                    (2 ^ p.1 * U) (2 ^ p.1 * U)
                    (2 ^ p.2 * V) (2 ^ p.2 * V)) *
                Real.log (x : ℝ) ^ 5 := by
  rcases smoothedTypeIIRectangleMean_le_log_five with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hxlog hU hV hD hDQ
  let P := typeIIBoundaryPairs x U V
  let J := characterIndicesIoc D Q
  let R : (k : ℕ) × DirichletCharacter ℂ k → ℕ × ℕ → ℂ :=
    fun χ p => smoothedTypeIIRectangle x U
      (2 ^ p.1 * U) (2 ^ p.1 * U)
      (2 ^ p.2 * V) (2 ^ p.2 * V) χ.2
  have hnorm (χ : (k : ℕ) × DirichletCharacter ℂ k) :
      ‖∑ p ∈ P, R χ p‖ ≤ ∑ p ∈ P, ‖R χ p‖ := norm_sum_le _ _
  rw [show (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖smoothedTypeIIBoundarySum x U V i.2‖) =
        ∑ i ∈ J, primitiveDyadicWeight i * ‖∑ p ∈ P, R i p‖ by
      rfl]
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
          (Real.exp 1 * (x : ℝ)) *
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q
                (2 ^ p.1 * U) (2 ^ p.1 * U)
                (2 ^ p.2 * V) (2 ^ p.2 * V)) *
            Real.log (x : ℝ) ^ 5 := by
      apply Finset.sum_le_sum
      intro p hp
      have hUp : 1 ≤ 2 ^ p.1 * U := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      have hVp : 1 ≤ 2 ^ p.2 * V := by
        exact Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
      simpa only [P, J, R] using
        hrectangle x U D Q
          (2 ^ p.1 * U) (2 ^ p.1 * U)
          (2 ^ p.2 * V) (2 ^ p.2 * V)
          hx hxlog hD hDQ hUp hVp (by omega) (by omega)

/-- Uniform boundary-sum estimate with the correct `Q²/x` conductor scale. -/
theorem smoothedTypeIIBoundarySumMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖smoothedTypeIIBoundarySum x U V i.2‖) ≤
            ((typeIIBoundaryPairs x U V).card : ℝ) *
              ((Real.exp 1 * (x : ℝ)) *
                Real.sqrt
                  (2 * C₀ ^ 2 * C₁ *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) *
                Real.log (x : ℝ) ^ 5) := by
  rcases smoothedTypeIIBoundarySumMean_le_majorants with
    ⟨C₀, C₁, hC₀, hC₁, hboundary⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hxlog hU hV hD hDQ
  let K : ℝ :=
    (Real.exp 1 * (x : ℝ)) *
      Real.sqrt
        (2 * C₀ ^ 2 * C₁ *
          typeIIBoundaryConductorScale D Q U V x *
          Real.log (2 * (x : ℝ)) ^ 5) *
      Real.log (x : ℝ) ^ 5
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖smoothedTypeIIBoundarySum x U V i.2‖) ≤
        ∑ p ∈ typeIIBoundaryPairs x U V,
          (Real.exp 1 * (x : ℝ)) *
            Real.sqrt
              (typeIISpectralRectangleMajorant C₀ C₁ D Q
                (2 ^ p.1 * U) (2 ^ p.1 * U)
                (2 ^ p.2 * V) (2 ^ p.2 * V)) *
            Real.log (x : ℝ) ^ 5 :=
      hboundary x U V D Q hx hxlog hU hV hD hDQ
    _ ≤ ∑ _p ∈ typeIIBoundaryPairs x U V, K := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [K]
      gcongr
      exact typeIISpectralRectangleMajorant_boundary_le
        C₀ C₁ D Q hC₁.le hD hU hV hp
    _ = ((typeIIBoundaryPairs x U V).card : ℝ) * K := by simp
    _ = ((typeIIBoundaryPairs x U V).card : ℝ) *
        ((Real.exp 1 * (x : ℝ)) *
          Real.sqrt
            (2 * C₀ ^ 2 * C₁ *
              typeIIBoundaryConductorScale D Q U V x *
              Real.log (2 * (x : ℝ)) ^ 5) *
          Real.log (x : ℝ) ^ 5) := rfl

end Chen.BombieriVinogradov
