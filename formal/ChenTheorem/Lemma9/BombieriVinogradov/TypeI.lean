import ChenTheorem.Lemma9.BombieriVinogradov.VaughanIdentity
import ChenTheorem.Lemma9.BombieriVinogradov.Bilinear
import ChenTheorem.Lemma6.PolyaVinogradov
import ChenTheorem.Lemma6.DivisorSquareMeanProof

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Type-I input for Bombieri--Vinogradov

The short-variable pieces of Vaughan's identity are controlled by uniform
character-prefix estimates and summation by parts.  This file isolates that
analytic input from the later convolution bookkeeping.
-/

/-- Twist a real arithmetic function by a Dirichlet character. -/
noncomputable def characterTwist {q : ℕ}
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * χ n, by simp⟩

@[simp]
theorem characterTwist_apply {q : ℕ}
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    characterTwist f χ n = (f n : ℂ) * χ n :=
  rfl

/-- Character twists commute with Dirichlet convolution. -/
theorem characterTwist_mul {q : ℕ}
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    characterTwist (f * g) χ = characterTwist f χ * characterTwist g χ := by
  ext n
  simp only [characterTwist_apply, ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hprod, Nat.cast_mul]
  rw [map_mul]
  ring

/-- Finite hyperbola identity for a character-twisted convolution. -/
theorem sum_characterTwist_mul_eq_sum_sum {q : ℕ}
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * χ n) =
      ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) * χ d *
        ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * χ m := by
  change (∑ n ∈ Finset.Ioc 0 N, characterTwist (f * g) χ n) =
    ∑ d ∈ Finset.Ioc 0 N, characterTwist f χ d *
      ∑ m ∈ Finset.Ioc 0 (N / d), characterTwist g χ m
  rw [characterTwist_mul]
  exact ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (characterTwist f χ) (characterTwist g χ) N

/-- Three-factor version of the finite twisted hyperbola identity. -/
theorem sum_characterTwist_mul_mul_eq_sum_sum_sum {q : ℕ}
    (f g h : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (((f * g) * h) n : ℂ) * χ n) =
      ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) * χ d *
        ∑ e ∈ Finset.Ioc 0 (N / d), (g e : ℂ) * χ e *
          ∑ k ∈ Finset.Ioc 0 ((N / d) / e), (h k : ℂ) * χ k := by
  rw [mul_assoc, sum_characterTwist_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_characterTwist_mul_eq_sum_sum]

/-- Exact hyperbola expansion of the first Type-I term in Vaughan's
identity.  Its outer coefficient is supported on `d ≤ U`. -/
theorem vaughanTypeIOneSum_eq_hyperbola {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIOneSum x U χ =
      ∑ d ∈ Finset.Ioc 0 x,
        (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
          χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
  rw [vaughanTypeIOneSum, vaughanTypeIOne]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  exact sum_characterTwist_mul_eq_sum_sum
    (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log χ x

/-- Changing the prefix convention from `range` to `[1,N]` does not alter a
Dirichlet-character sum at a nontrivial modulus. -/
theorem character_sum_Icc_eq_range {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, χ n) = ∑ n ∈ Finset.range (N + 1), χ n := by
  have hzero : χ (0 : ZMod q) = 0 :=
    χ.map_zero' (by omega)
  rw [show Finset.range (N + 1) =
      insert 0 (Finset.Icc 1 N) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp), Nat.cast_zero, hzero, zero_add]

/-- Pólya--Vinogradov in the `[1,N]` prefix convention used by the
Bombieri--Vinogradov sums. -/
theorem primitive_character_sum_Icc_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) := by
  rw [character_sum_Icc_eq_range hq χ N]
  exact primitive_character_prefix_sum_norm_le hχ hq (N + 1)

/-- The total variation of `log` on the positive integers below `N`. -/
theorem sum_log_succ_sub_log_Ioc (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 (N - 1),
      (Real.log (n + 1 : ℕ) - Real.log n)) = Real.log N := by
  have hset : Finset.Ioc 0 (N - 1) =
      (Finset.range N).erase 0 := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hset]
  calc
    (∑ n ∈ (Finset.range N).erase 0,
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) =
        (∑ n ∈ (Finset.range N).erase 0,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) +
          (Real.log ((0 + 1 : ℕ) : ℝ) - Real.log (0 : ℝ)) := by norm_num
    _ = ∑ n ∈ Finset.range N,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :=
      by
        simpa only [Nat.cast_zero] using
          ((Finset.range N).sum_erase_add (a := 0)
            (fun n => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
            (Finset.mem_range.mpr (by omega)))
    _ = Real.log (N : ℝ) - Real.log (0 : ℝ) := by
      convert (Finset.sum_range_sub
        (fun n : ℕ => Real.log (n : ℝ)) N) using 1
      all_goals norm_num
    _ = Real.log N := by rw [Real.log_zero, sub_zero]

/-- Abel summation turns the uniform Pólya--Vinogradov prefix bound into a
logarithmically weighted character-sum bound. -/
theorem primitive_character_log_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) (hN : 2 ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) * Real.log N := by
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  let S : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, χ n
  have hprefix (k : ℕ) : ‖S k‖ ≤ B := by
    dsimp only [S, B]
    exact primitive_character_prefix_sum_norm_le hχ hq k
  have habel := Finset.sum_Ioc_by_parts
    (f := fun n : ℕ => (Real.log n : ℂ))
    (g := fun n : ℕ => χ n) (m := 0) (n := N) (by omega)
  have hlogone :
      ((Real.log (((0 + 1 : ℕ) : ℝ)) : ℂ)) = 0 := by norm_num
  simp only [smul_eq_mul] at habel
  rw [hlogone, zero_mul, sub_zero] at habel
  have habel' :
      (∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n) =
        (Real.log N : ℂ) * S (N + 1) -
          ∑ n ∈ Finset.Ioc 0 (N - 1),
            ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1) := by
    simpa only [smul_eq_mul, S, Complex.ofReal_sub] using habel
  rw [habel']
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hdelta (n : ℕ) (hn : n ∈ Finset.Ioc 0 (N - 1)) :
      0 ≤ Real.log (n + 1 : ℕ) - Real.log n := by
    have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hnpos)
      (by exact_mod_cast Nat.le_succ n))
  calc
    ‖(Real.log N : ℂ) * S (N + 1) -
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1)‖ ≤
        ‖(Real.log N : ℂ) * S (N + 1)‖ +
          ‖∑ n ∈ Finset.Ioc 0 (N - 1),
            ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1)‖ :=
      norm_sub_le _ _
    _ ≤ Real.log N * B +
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          (Real.log (n + 1 : ℕ) - Real.log n) * B := by
      gcongr
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlogN]
        exact mul_le_mul_of_nonneg_left (hprefix (N + 1)) hlogN
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hdelta n hn)]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1)) (hdelta n hn)
    _ = 2 * B * Real.log N := by
      rw [← Finset.sum_mul, sum_log_succ_sub_log_Ioc N (by omega)]
      ring
    _ = 6 * Real.sqrt q * Real.log (2 * q) * Real.log N := by
      dsimp only [B]
      ring

/-- Totalized form of the logarithmically weighted bound. -/
theorem primitive_character_log_sum_norm_le_all
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) *
        Real.log ((max 2 N : ℕ) : ℝ) := by
  by_cases hN : 2 ≤ N
  · simpa [max_eq_right hN] using
      primitive_character_log_sum_norm_le hχ hq N hN
  · have hsmall : N = 0 ∨ N = 1 := by omega
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    have hnonneg :
        0 ≤ 6 * Real.sqrt q * Real.log (2 * q) * Real.log 2 := by
      positivity
    rcases hsmall with rfl | rfl <;> norm_num <;> exact hnonneg

/-- The exact first Type-I hyperbola sum with the outer support made
explicit. -/
theorem vaughanTypeIOneSum_eq_short_hyperbola {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIOneSum x U χ =
      ∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
  rw [vaughanTypeIOneSum_eq_hyperbola]
  let term : ℕ → ℂ := fun d =>
    (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
      χ d *
        ∑ m ∈ Finset.Ioc 0 (x / d),
          (ArithmeticFunction.log m : ℂ) * χ m
  calc
    (∑ d ∈ Finset.Ioc 0 x,
        (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
          χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m) =
        ∑ d ∈ Finset.Ioc 0 (min U x), term d := by
      symm
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_Ioc.mp hd
        exact Finset.mem_Ioc.mpr ⟨hd'.1, hd'.2.trans (min_le_right U x)⟩
      · intro d hdx hdnot
        have hddata := Finset.mem_Ioc.mp hdx
        have hUd : U < d := by
          by_contra h
          exact hdnot (Finset.mem_Ioc.mpr
            ⟨hddata.1, le_min (le_of_not_gt h) hddata.2⟩)
        simp [term, truncateLE_apply, Nat.not_le.mpr hUd]
    _ = ∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdU : d ≤ U :=
        (Finset.mem_Ioc.mp hd).2.trans (min_le_left U x)
      simp [term, truncateLE_apply, hdU]

/-- Pointwise Type-I bound for the first Vaughan piece.  The important
feature is the short factor `min U x`. -/
theorem norm_vaughanTypeIOneSum_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (x U : ℕ) (hx : 2 ≤ x) :
    ‖vaughanTypeIOneSum x U χ‖ ≤
      6 * (min U x : ℝ) * Real.sqrt q *
        Real.log (2 * q) * Real.log x := by
  rw [vaughanTypeIOneSum_eq_short_hyperbola]
  let C : ℝ := 6 * Real.sqrt q * Real.log (2 * q) * Real.log x
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    ‖∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m‖ ≤
        ∑ d ∈ Finset.Ioc 0 (min U x),
          ‖(ArithmeticFunction.moebius d : ℂ) * χ d *
            ∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Ioc 0 (min U x), C := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hmax : max 2 (x / d) ≤ x :=
        max_le hx (Nat.div_le_self x d)
      have hlogmax :
          Real.log ((max 2 (x / d) : ℕ) : ℝ) ≤ Real.log x := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hmax)
      have hinner := primitive_character_log_sum_norm_le_all
        hχ hq (x / d)
      have hinnerC :
          ‖∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ ≤ C := by
        exact hinner.trans (by
          dsimp only [C]
          gcongr)
      have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hchar : ‖χ d‖ ≤ 1 := DirichletCharacter.norm_le_one χ d
      rw [norm_mul, norm_mul]
      calc
        ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖χ d‖ *
            ‖∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ ≤
            1 * 1 * C := by gcongr
        _ = C := by ring
    _ = (min U x : ℝ) * C := by simp
    _ = 6 * (min U x : ℝ) * Real.sqrt q *
          Real.log (2 * q) * Real.log x := by
      dsimp only [C]
      ring

/-- The short convolution occurring in Vaughan's second Type-I piece. -/
noncomputable def vaughanTypeIShortCoefficient (U V : ℕ) :
    ArithmeticFunction ℝ :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateLE ArithmeticFunction.vonMangoldt V

theorem vaughanTypeITwo_eq_shortCoefficient (U V : ℕ) :
    vaughanTypeITwo U V =
      truncateLE ArithmeticFunction.vonMangoldt V -
        vaughanTypeIShortCoefficient U V * ArithmeticFunction.zeta := by
  rfl

/-- The short Type-I convolution is supported on products at most `U*V`. -/
theorem vaughanTypeIShortCoefficient_eq_zero_of_lt
    (U V n : ℕ) (hn : U * V < n) :
    vaughanTypeIShortCoefficient U V n = 0 := by
  rw [vaughanTypeIShortCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hd : p.1 ≤ U
  · by_cases he : p.2 ≤ V
    · have hpUV : p.1 * p.2 ≤ U * V := Nat.mul_le_mul hd he
      omega
    · simp [truncateLE_apply, hd, he]
  · simp [truncateLE_apply, hd]

/-- Exact hyperbola expansion of Vaughan's second Type-I term. -/
theorem vaughanTypeITwoSum_eq_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeITwoSum x U V χ =
      (∑ n ∈ Finset.Ioc 0 x,
        (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n) -
      ∑ m ∈ Finset.Ioc 0 x,
        (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeITwoSum, vaughanTypeITwo_eq_shortCoefficient]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply]
  push_cast
  simp_rw [add_mul, neg_mul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    sum_characterTwist_mul_eq_sum_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
  simp [ArithmeticFunction.zeta_apply, hnpos]

/-- The two genuinely short supports in Vaughan's second Type-I term made
explicit.  This is the form used for pointwise Pólya--Vinogradov estimates:
the direct von-Mangoldt piece has length at most `V`, and the outer
convolution variable has length at most `U*V`. -/
theorem vaughanTypeITwoSum_eq_short_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeITwoSum x U V χ =
      (∑ n ∈ Finset.Ioc 0 (min V x),
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
      ∑ m ∈ Finset.Ioc 0 (min (U * V) x),
        (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeITwoSum_eq_hyperbola]
  congr 1
  · let term : ℕ → ℂ := fun n =>
      (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n
    calc
      (∑ n ∈ Finset.Ioc 0 x,
          (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n) =
          ∑ n ∈ Finset.Ioc 0 (min V x), term n := by
        symm
        apply Finset.sum_subset
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Ioc.mpr
            ⟨hn'.1, hn'.2.trans (min_le_right V x)⟩
        · intro n hnx hnnot
          have hndata := Finset.mem_Ioc.mp hnx
          have hVn : V < n := by
            by_contra h
            exact hnnot (Finset.mem_Ioc.mpr
              ⟨hndata.1, le_min (le_of_not_gt h) hndata.2⟩)
          simp [term, truncateLE_apply, Nat.not_le.mpr hVn]
      _ = ∑ n ∈ Finset.Ioc 0 (min V x),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnV : n ≤ V :=
          (Finset.mem_Ioc.mp hn).2.trans (min_le_left V x)
        simp [term, truncateLE_apply, hnV]
  · let term : ℕ → ℂ := fun m =>
      (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
        ∑ n ∈ Finset.Ioc 0 (x / m), χ n
    change (∑ m ∈ Finset.Ioc 0 x, term m) =
      ∑ m ∈ Finset.Ioc 0 (min (U * V) x), term m
    symm
    apply Finset.sum_subset
    · intro m hm
      have hm' := Finset.mem_Ioc.mp hm
      exact Finset.mem_Ioc.mpr
        ⟨hm'.1, hm'.2.trans (min_le_right (U * V) x)⟩
    · intro m hmx hmnot
      have hmdata := Finset.mem_Ioc.mp hmx
      have hUVm : U * V < m := by
        by_contra h
        exact hmnot (Finset.mem_Ioc.mpr
          ⟨hmdata.1, le_min (le_of_not_gt h) hmdata.2⟩)
      dsimp only [term]
      rw [vaughanTypeIShortCoefficient_eq_zero_of_lt U V m hUVm]
      simp

/-- A cutoff-independent divisor bound for the short coefficient in
Vaughan's second Type-I term. -/
theorem abs_vaughanTypeIShortCoefficient_le
    (U V n : ℕ) :
    |vaughanTypeIShortCoefficient U V n| ≤
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIShortCoefficient]
  rw [vaughanTypeIShortCoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateLE ArithmeticFunction.vonMangoldt V p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1pos : 0 < p.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2pos : 0 < p.2 :=
        Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2dvd : p.2 ∣ n :=
        ⟨p.1, by simpa [mul_comm] using hpdata.1.symm⟩
      have hp2le : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2dvd
      have hlogmono : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      have hmu :
          |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateLE_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      have hlambda :
          |truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤ Real.log n := by
        rw [truncateLE_apply]
        split_ifs
        · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact ArithmeticFunction.vonMangoldt_le_log.trans hlogmono
        · rw [abs_zero]
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [abs_mul]
      calc
        |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| *
            |truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤
            1 * Real.log n := by gcongr
        _ = Real.log n := one_mul _
    _ = (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by simp

/-- Divisor-square `L²` bound for the short Type-I coefficient. -/
theorem vaughanTypeIShortCoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
          C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V X hX
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          (Real.log (X : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hndata := Finset.mem_Icc.mp hn
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hndata.1)
      have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hndata.2)
      have habs := abs_vaughanTypeIShortCoefficient_le U V n
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |vaughanTypeIShortCoefficient U V n| ^ 2 ≤
            ((n.divisorsAntidiagonal.card : ℝ) * Real.log n) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ ((n.divisorsAntidiagonal.card : ℝ) * Real.log X) ^ 2 := by
          gcongr
        _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
            (Real.log X) ^ 2 := by ring
    _ = (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2) *
        (Real.log X) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (C * (X : ℝ) * (Real.log X) ^ 3) *
        (Real.log X) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmean X hX) (sq_nonneg _)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by ring

/-- A deliberately coarse `L¹` consequence of the divisor-square estimate.
It is sufficient here because the support length `U*V` will be chosen
polylogarithmic in the final Bombieri--Vinogradov assembly. -/
theorem vaughanTypeIShortCoefficient_norm_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V W : ℕ), W = U * V → 2 ≤ W →
      (∑ m ∈ Finset.Ioc 0 W,
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) ≤
        C * (W : ℝ) * (Real.log (W : ℝ)) ^ 5 + (W : ℝ) := by
  rcases vaughanTypeIShortCoefficient_sq_mean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V W hW hW2
  have hsets : Finset.Ioc 0 W = Finset.Icc 1 W := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  calc
    (∑ m ∈ Finset.Ioc 0 W,
        ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) ≤
        ∑ m ∈ Finset.Ioc 0 W,
          (‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [sq_nonneg
        (‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ - (1 / 2 : ℝ))]
    _ = (∑ m ∈ Finset.Icc 1 W,
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ ^ 2) + (W : ℝ) := by
      rw [Finset.sum_add_distrib, hsets]
      simp
    _ ≤ C * (W : ℝ) * (Real.log (W : ℝ)) ^ 5 + (W : ℝ) := by
      exact add_le_add_left (hmean U V W hW2) _

/-- Complete pointwise estimate for Vaughan's second Type-I piece.  Both
outer supports are short; the remaining character prefix is bounded by
Pólya--Vinogradov. -/
theorem norm_vaughanTypeITwoSum_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → 2 ≤ q →
        ∀ (x U V : ℕ), 2 ≤ x → 2 ≤ U * V → U * V ≤ x →
          ‖vaughanTypeITwoSum x U V χ‖ ≤
            (V : ℝ) * Real.log x +
              3 * (C * ((U * V : ℕ) : ℝ) *
                    (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                      ((U * V : ℕ) : ℝ)) *
                Real.sqrt q * Real.log (2 * q) := by
  rcases vaughanTypeIShortCoefficient_norm_sum_le with ⟨C, hC, hcoeff⟩
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ hq x U V hx hUV2 hUVx
  have hUpos : 1 ≤ U := by
    by_contra h
    have : U = 0 := by omega
    subst U
    simp at hUV2
  have hVx : V ≤ x := by
    have hVUV : V ≤ U * V := by
      simpa using Nat.mul_le_mul_right V hUpos
    exact hVUV.trans hUVx
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hpvFactor : 0 ≤ 3 * Real.sqrt (q : ℝ) * Real.log (2 * q) := by
    positivity
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hdirect :
      ‖∑ n ∈ Finset.Ioc 0 V,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
        (V : ℝ) * Real.log x := by
    calc
      ‖∑ n ∈ Finset.Ioc 0 V,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
          ∑ n ∈ Finset.Ioc 0 V,
            ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc 0 V, Real.log x := by
        apply Finset.sum_le_sum
        intro n hn
        have hndata := Finset.mem_Ioc.mp hn
        have hnx : n ≤ x := hndata.2.trans hVx
        have hlogn : Real.log (n : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log (by exact_mod_cast hndata.1)
            (by exact_mod_cast hnx)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc
          ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤
              Real.log n * 1 := by
            gcongr
            · exact ArithmeticFunction.vonMangoldt_le_log
            · exact DirichletCharacter.norm_le_one χ n
          _ ≤ Real.log x := by simpa using hlogn
      _ = (V : ℝ) * Real.log x := by simp
  have hpv (m : ℕ) :
      ‖∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
        3 * Real.sqrt q * Real.log (2 * q) := by
    have hset : Finset.Ioc 0 (x / m) = Finset.Icc 1 (x / m) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    exact primitive_character_sum_Icc_norm_le hχ hq (x / m)
  have hcoeff' := hcoeff U V (U * V) rfl hUV2
  have hhyper :
      ‖∑ m ∈ Finset.Ioc 0 (U * V),
          (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
            ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
        3 * (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
          Real.sqrt q * Real.log (2 * q) := by
    calc
      ‖∑ m ∈ Finset.Ioc 0 (U * V),
          (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
            ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
          ∑ m ∈ Finset.Ioc 0 (U * V),
            ‖(vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
              ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 (U * V),
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, norm_mul]
        have hchar := DirichletCharacter.norm_le_one χ m
        have hinner := hpv m
        calc
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ * ‖χ m‖ *
              ‖∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
              ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ * 1 *
                (3 * Real.sqrt q * Real.log (2 * q)) := by
            gcongr
          _ = ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ *
                (3 * Real.sqrt q * Real.log (2 * q)) := by ring
      _ = (∑ m ∈ Finset.Ioc 0 (U * V),
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        rw [Finset.sum_mul]
      _ ≤ (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        apply mul_le_mul_of_nonneg_right hcoeff'
        exact hpvFactor
      _ = 3 * (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
            Real.sqrt q * Real.log (2 * q) := by ring
  rw [vaughanTypeITwoSum_eq_short_hyperbola,
    min_eq_left hVx, min_eq_left hUVx]
  exact (norm_sub_le _ _).trans (add_le_add hdirect hhyper)

/-- Dyadic rectangular large-sieve estimate for the short coefficient in
Vaughan's second Type-I term. -/
theorem vaughanTypeIShortRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U V D Q M N K L : ℕ), 1 ≤ D → D ≤ Q → 2 ≤ M + N →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N
                (fun n => (vaughanTypeIShortCoefficient U V n : ℂ)) i.2‖ *
              ‖characterIntervalSum K L (fun _ => (1 : ℂ)) i.2‖) ^ 2 ≤
          (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              (C₁ * ((M + N : ℕ) : ℝ) *
                (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
            (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) * (L : ℝ)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIShortCoefficient_sq_mean with ⟨C₁, hC₁, hcoeffMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U V D Q M N K L hD hDQ hMN
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
          C₁ * ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (M + N),
          ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIShortCoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

end Chen.BombieriVinogradov
