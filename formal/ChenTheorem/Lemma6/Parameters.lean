/-
Parameter choices in equations (19) and (20) of Chen's proof.

We keep the paper's real scales separate from their natural-number cutoffs.
The lemmas below show that `floor` and `ceil` change these scales by at most
an absolute factor once the corresponding block is occupied.  This is the
bookkeeping needed before simplifying the moment majorants.
-/
import ChenTheorem.Lemma6.Integration
import ChenTheorem.Lemma6.RemainderConnection

open Real

namespace Chen

/-- Chen's choice `H = D (log x)^100 I_{l,x}` in equation (19). -/
noncomputable def lemma6Equation19HScale (x l : ℕ) : ℝ :=
  lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
    lemma6ExceptionalFactorAt x l

/-- Natural cutoff corresponding to the real parameter in equation (19). -/
noncomputable def lemma6Equation19HCutoff (x l : ℕ) : ℕ :=
  ⌈lemma6Equation19HScale x l⌉₊

/-- The first entry in Chen's maximum defining `H` in equation (20),
written invariantly as `D² Y⁻¹ (log x)^200 I_{l,x}`. -/
noncomputable def lemma6Equation20HFirstScale (x l k : ℕ) : ℝ :=
  lemma6DyadicModulusScale x l ^ 2 /
      lemma6PairDyadicScale x k *
    (Real.log x) ^ 200 * lemma6ExceptionalFactorAt x l

/-- Chen's real `H` parameter in equation (20). -/
noncomputable def lemma6Equation20HScale
    (x l k : ℕ) (ε : ℝ) : ℝ :=
  max (lemma6Equation20HFirstScale x l k)
    ((x : ℝ) ^ ((1 : ℝ) / 2 - ε))

/-- Natural cutoff corresponding to the real parameter in equation (20). -/
noncomputable def lemma6Equation20HCutoff
    (x l k : ℕ) (ε : ℝ) : ℕ :=
  ⌈lemma6Equation20HScale x l k ε⌉₊

theorem lemma6DyadicModulusScale_nonneg (x l : ℕ) :
    0 ≤ lemma6DyadicModulusScale x l := by
  unfold lemma6DyadicModulusScale
  positivity

theorem lemma6PairDyadicScale_nonneg (x k : ℕ) :
    0 ≤ lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  positivity

theorem lemma6PairDyadicScale_pos {x : ℕ} (hx : 1 ≤ x) (k : ℕ) :
    0 < lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  positivity

theorem lemma6Equation19HScale_nonneg (x l : ℕ) :
    0 ≤ lemma6Equation19HScale x l := by
  unfold lemma6Equation19HScale
  exact mul_nonneg
    (mul_nonneg (lemma6DyadicModulusScale_nonneg x l) (by positivity))
    (lemma6ExceptionalFactor_pos _).le

theorem lemma6Equation20HFirstScale_nonneg (x l k : ℕ) :
    0 ≤ lemma6Equation20HFirstScale x l k := by
  unfold lemma6Equation20HFirstScale
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (sq_nonneg _) (lemma6PairDyadicScale_nonneg x k))
      (by positivity))
    (lemma6ExceptionalFactor_pos _).le

theorem lemma6Equation20HScale_nonneg
    (x l k : ℕ) (ε : ℝ) :
    0 ≤ lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_of_le_left (lemma6Equation20HFirstScale_nonneg x l k)

/-- The upper modulus cutoff differs from the paper's real endpoint by
less than one. -/
theorem lemma6ModulusCutoff_cast_lt_scale_add_one (x l : ℕ) :
    (lemma6ModulusCutoff x l : ℝ) <
      lemma6DyadicModulusScale x l + 1 := by
  unfold lemma6ModulusCutoff lemma6DyadicModulusScale
  exact Nat.ceil_lt_add_one (by positivity)

theorem lemma6DyadicModulusScale_le_modulusCutoff (x l : ℕ) :
    lemma6DyadicModulusScale x l ≤
      (lemma6ModulusCutoff x l : ℝ) := by
  unfold lemma6ModulusCutoff lemma6DyadicModulusScale
  exact Nat.le_ceil _

/-- For positive blocks, the real lower endpoint is exactly `D/2`. -/
theorem lemma6_modulusLowerReal_eq_half_scale
    {x l : ℕ} (hl : 1 ≤ l) :
    (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 =
      lemma6DyadicModulusScale x l / 2 := by
  unfold lemma6DyadicModulusScale
  have hpow : (2 : ℝ) ^ l = 2 * (2 : ℝ) ^ (l - 1) := by
    calc
      (2 : ℝ) ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by ring
  rw [hpow]
  ring

theorem lemma6_half_scale_sub_one_lt_modulusLowerCutoff
    {x l : ℕ} (hl : 1 ≤ l) :
    lemma6DyadicModulusScale x l / 2 - 1 <
      (lemma6ModulusLowerCutoff x l : ℝ) := by
  unfold lemma6ModulusLowerCutoff
  rw [← lemma6_modulusLowerReal_eq_half_scale hl]
  exact Nat.sub_one_lt_floor _

/-- Once `D ≥ 4`, the floored lower endpoint is still at least `D/4`. -/
theorem lemma6_quarter_scale_le_modulusLowerCutoff
    {x l : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6DyadicModulusScale x l / 4 ≤
      (lemma6ModulusLowerCutoff x l : ℝ) := by
  have hfloor :=
    lemma6_half_scale_sub_one_lt_modulusLowerCutoff (x := x) hl
  have : lemma6DyadicModulusScale x l / 4 ≤
      lemma6DyadicModulusScale x l / 2 - 1 := by linarith
  exact this.trans hfloor.le

theorem lemma6ModulusCutoff_cast_le_five_quarters_scale
    {x l : ℕ} (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    (lemma6ModulusCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l := by
  have hceil := lemma6ModulusCutoff_cast_lt_scale_add_one x l
  linarith

/-- The lower pair-product cutoff differs from `Y` by less than one. -/
theorem lemma6_pairScale_sub_one_lt_pairLowerCutoff (x k : ℕ) :
    lemma6PairDyadicScale x k - 1 <
      (lemma6PairLowerCutoff x k : ℝ) := by
  unfold lemma6PairLowerCutoff
  exact Nat.sub_one_lt_floor _

theorem lemma6PairLowerCutoff_le_pairScale (x k : ℕ) :
    (lemma6PairLowerCutoff x k : ℝ) ≤
      lemma6PairDyadicScale x k := by
  unfold lemma6PairLowerCutoff
  exact Nat.floor_le (lemma6PairDyadicScale_nonneg x k)

theorem lemma6_pairScale_eq_half_next (x k : ℕ) :
    lemma6PairDyadicScale x (k + 1) =
      2 * lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  rw [pow_succ]
  ring

theorem lemma6PairUpperCutoff_cast_lt_two_mul_scale_add_one
    (x k : ℕ) :
    (lemma6PairUpperCutoff x k : ℝ) <
      2 * lemma6PairDyadicScale x k + 1 := by
  unfold lemma6PairUpperCutoff
  rw [← lemma6_pairScale_eq_half_next]
  exact Nat.ceil_lt_add_one (lemma6PairDyadicScale_nonneg x (k + 1))

theorem lemma6PairUpperCutoff_cast_le_five_halves_scale
    {x k : ℕ} (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6PairUpperCutoff x k : ℝ) ≤
      (5 / 2 : ℝ) * lemma6PairDyadicScale x k := by
  have hceil :=
    lemma6PairUpperCutoff_cast_lt_two_mul_scale_add_one x k
  linarith

theorem lemma6PairScale_le_pairUpperCutoff (x k : ℕ) :
    lemma6PairDyadicScale x k ≤
      (lemma6PairUpperCutoff x k : ℝ) := by
  calc
    lemma6PairDyadicScale x k ≤
        lemma6PairDyadicScale x (k + 1) := by
      rw [lemma6_pairScale_eq_half_next]
      have hY := lemma6PairDyadicScale_nonneg x k
      linarith
    _ ≤ (lemma6PairUpperCutoff x k : ℝ) := by
      unfold lemma6PairUpperCutoff
      exact Nat.le_ceil _

/-- Uniform replacement of the natural modulus cutoffs by the real scale
`D`.  This single estimate is used in every moment majorant in (19) and
(20). -/
theorem lemma6_modulus_cutoff_add_div_le_scale
    {x l : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    {N : ℝ} (hN : 0 ≤ N) :
    (lemma6ModulusCutoff x l : ℝ) +
        N / (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * N / lemma6DyadicModulusScale x l := by
  let D := lemma6DyadicModulusScale x l
  let R := (lemma6ModulusLowerCutoff x l : ℝ)
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hRlower : D / 4 ≤ R := by
    simpa only [D, R] using
      lemma6_quarter_scale_le_modulusLowerCutoff hl hD
  have hRpos : 0 < R := (div_pos hDpos (by norm_num)).trans_le hRlower
  have hcoef : 0 ≤ 4 * N / D := by positivity
  have heq : (4 * N / D) * (D / 4) = N := by
    field_simp
  have hquot : N / R ≤ 4 * N / D := by
    apply (div_le_iff₀ hRpos).2
    calc
      N = (4 * N / D) * (D / 4) := heq.symm
      _ ≤ (4 * N / D) * R :=
        mul_le_mul_of_nonneg_left hRlower hcoef
  exact add_le_add
    (lemma6ModulusCutoff_cast_le_five_quarters_scale hD) hquot

/-- Pair-second-moment scale in equation (19), with all floor/ceil effects
absorbed into absolute constants. -/
theorem lemma6_pairSecond_cutoff_factor_le
    {x l k : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6ModulusCutoff x l : ℝ) +
        ((lemma6PairUpperCutoff x k -
          lemma6PairLowerCutoff x k : ℕ) : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l := by
  let N : ℝ := ((lemma6PairUpperCutoff x k -
    lemma6PairLowerCutoff x k : ℕ) : ℝ)
  have hN : 0 ≤ N := by positivity
  have hbase := lemma6_modulus_cutoff_add_div_le_scale hl hD hN
  have hNle : N ≤ (5 / 2 : ℝ) * lemma6PairDyadicScale x k := by
    calc
      N ≤ (lemma6PairUpperCutoff x k : ℝ) := by
        dsimp only [N]
        exact_mod_cast Nat.sub_le _ _
      _ ≤ (5 / 2 : ℝ) * lemma6PairDyadicScale x k :=
        lemma6PairUpperCutoff_cast_le_five_halves_scale hY
  have hDpos : 0 < lemma6DyadicModulusScale x l :=
    lt_of_lt_of_le (by norm_num) hD
  have hquot :
      4 * N / lemma6DyadicModulusScale x l ≤
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith
  exact hbase.trans (add_le_add_right hquot _)

theorem lemma6PairSecondMajorant_beta_le_scales
    {x l m k : ℕ} (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν) ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l) *
        (1 + Real.log (lemma6PairUpperCutoff x k)) := by
  have hlog0 :
      0 ≤ 1 + Real.log (lemma6PairUpperCutoff x k : ℕ) := by
    have hU : (1 : ℝ) ≤ lemma6PairUpperCutoff x k := by
      calc
        (1 : ℝ) ≤ lemma6PairDyadicScale x k := by linarith
        _ ≤ (lemma6PairUpperCutoff x k : ℝ) :=
          lemma6PairScale_le_pairUpperCutoff x k
    exact add_nonneg zero_le_one (Real.log_nonneg hU)
  exact (lemma6PairSecondMajorant_beta_le_log x l m k ν hxlog).trans
    (mul_le_mul_of_nonneg_right
      (lemma6_pairSecond_cutoff_factor_le hl hD hY) hlog0)

theorem lemma6MollifierSecondMajorant_le_scales
    {x l H : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6MollifierSecondMajorant x l H ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * (H : ℝ) / lemma6DyadicModulusScale x l) *
        (1 + Real.log H) := by
  unfold lemma6MollifierSecondMajorant
  have hfactor := lemma6_modulus_cutoff_add_div_le_scale
    hl hD (show (0 : ℝ) ≤ H by positivity)
  have hlog0 : 0 ≤ 1 + Real.log (H : ℕ) := by
    by_cases hH : H = 0
    · subst H
      norm_num
    · exact add_nonneg zero_le_one
        (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hH)))
  exact mul_le_mul_of_nonneg_right hfactor hlog0

theorem lemma6MollifierFourthMajorant_le_scales
    {x l H : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6MollifierFourthMajorant x l H ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * ((H * H : ℕ) : ℝ) /
          lemma6DyadicModulusScale x l) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  unfold lemma6MollifierFourthMajorant
  exact mul_le_mul_of_nonneg_right
    (lemma6_modulus_cutoff_add_div_le_scale hl hD
      (show (0 : ℝ) ≤ (H * H : ℕ) by positivity))
    (by positivity)

theorem lemma6_pairFourth_cutoff_factor_le
    {x l k : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l := by
  let U : ℝ := lemma6PairUpperCutoff x k
  have hU0 : 0 ≤ U := by positivity
  have hY0 : 0 ≤ lemma6PairDyadicScale x k :=
    lemma6PairDyadicScale_nonneg x k
  have hUsq : U ^ 2 ≤ (25 / 4 : ℝ) *
      lemma6PairDyadicScale x k ^ 2 := by
    have hU := lemma6PairUpperCutoff_cast_le_five_halves_scale hY
    nlinarith [sq_nonneg
      ((5 / 2 : ℝ) * lemma6PairDyadicScale x k - U)]
  have hbase := lemma6_modulus_cutoff_add_div_le_scale hl hD
    (show 0 ≤ U ^ 2 by positivity)
  have hDpos : 0 < lemma6DyadicModulusScale x l :=
    lt_of_lt_of_le (by norm_num) hD
  have hquot :
      4 * U ^ 2 / lemma6DyadicModulusScale x l ≤
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith
  simpa only [U, Nat.cast_pow] using
    hbase.trans (add_le_add_right hquot _)

theorem lemma6PairFourthMajorant_beta_le_scales :
    ∃ C : ℝ, 0 < C ∧ ∀ (x l m k : ℕ) (ν : ℝ),
      3 ≤ Real.log (x : ℝ) → 1 ≤ l →
      4 ≤ lemma6DyadicModulusScale x l →
      2 ≤ lemma6PairDyadicScale x k →
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
  rcases lemma6PairFourthMajorant_beta_le_log_four with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k ν hxlog hl hD hY
  have hUreal : (2 : ℝ) ≤ lemma6PairUpperCutoff x k := by
    calc
      (2 : ℝ) ≤ lemma6PairDyadicScale x k := hY
      _ ≤ (lemma6PairUpperCutoff x k : ℝ) :=
        lemma6PairScale_le_pairUpperCutoff x k
  have hU : 2 ≤ lemma6PairUpperCutoff x k := by exact_mod_cast hUreal
  have hU2 : 2 ≤ lemma6PairUpperCutoff x k ^ 2 := by nlinarith
  have hfactor := lemma6_pairFourth_cutoff_factor_le hl hD hY
  calc
    lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 :=
      hraw x l m k ν hxlog hU2
    _ ≤ C * ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
      gcongr

theorem lemma6DerivativeFourthMajorant_le_kernel
    {x l : ℕ} (ν : ℝ) (hxlog : 2 ≤ Real.log (x : ℝ)) :
    lemma6DerivativeFourthMajorant x l ν ≤
      (2 : ℝ) ^ l * (Real.log x) ^ 110 * (1 + ν ^ 2) := by
  unfold lemma6DerivativeFourthMajorant
  exact mul_le_mul_of_nonneg_left
    (lemma6BetaPoint_norm_sq_le hxlog ν)
    (by positivity)

theorem lemma6_half_pairScale_le_pairLowerCutoff
    {x k : ℕ} (hY : 2 ≤ lemma6PairDyadicScale x k) :
    lemma6PairDyadicScale x k / 2 ≤
      (lemma6PairLowerCutoff x k : ℝ) := by
  have hfloor := lemma6_pairScale_sub_one_lt_pairLowerCutoff x k
  have : lemma6PairDyadicScale x k / 2 ≤
      lemma6PairDyadicScale x k - 1 := by linarith
  exact this.trans hfloor.le

theorem lemma6Equation19HScale_le_cutoff (x l : ℕ) :
    lemma6Equation19HScale x l ≤
      (lemma6Equation19HCutoff x l : ℝ) := by
  unfold lemma6Equation19HCutoff
  exact Nat.le_ceil _

theorem lemma6Equation19HCutoff_cast_lt_scale_add_one (x l : ℕ) :
    (lemma6Equation19HCutoff x l : ℝ) <
      lemma6Equation19HScale x l + 1 := by
  unfold lemma6Equation19HCutoff
  exact Nat.ceil_lt_add_one (lemma6Equation19HScale_nonneg x l)

theorem lemma6Equation20HScale_le_cutoff
    (x l k : ℕ) (ε : ℝ) :
    lemma6Equation20HScale x l k ε ≤
      (lemma6Equation20HCutoff x l k ε : ℝ) := by
  unfold lemma6Equation20HCutoff
  exact Nat.le_ceil _

theorem lemma6Equation20HCutoff_cast_lt_scale_add_one
    (x l k : ℕ) (ε : ℝ) :
    (lemma6Equation20HCutoff x l k ε : ℝ) <
      lemma6Equation20HScale x l k ε + 1 := by
  unfold lemma6Equation20HCutoff
  exact Nat.ceil_lt_add_one (lemma6Equation20HScale_nonneg x l k ε)

theorem lemma6Equation20HFirstScale_le_HScale
    (x l k : ℕ) (ε : ℝ) :
    lemma6Equation20HFirstScale x l k ≤
      lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_left _ _

theorem lemma6_threshold_le_Equation20HScale
    (x l k : ℕ) (ε : ℝ) :
    (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤
      lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_right _ _

/-- Algebraic simplification of the first equation-(20) parameter. -/
theorem lemma6Equation20HFirstScale_eq_paper
    {x : ℕ} (hx : 1 ≤ x) (l k : ℕ) (hk : k ≤ 2 * l) :
    lemma6Equation20HFirstScale x l k =
      (2 : ℝ) ^ (2 * l - k) *
        (x : ℝ) ^ (-(13 : ℝ) / 30) *
        (Real.log x) ^ 400 * lemma6ExceptionalFactorAt x l := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have htwoPow : (2 : ℝ) ^ (2 * l) * ((2 : ℝ) ^ k)⁻¹ =
      (2 : ℝ) ^ (2 * l - k) := by
    field_simp
    rw [← pow_add]
    congr 1
    omega
  have hxpow : ((x : ℝ) ^ ((13 : ℝ) / 30))⁻¹ =
      (x : ℝ) ^ (-(13 : ℝ) / 30) := by
    rw [← Real.rpow_neg hxR.le]
    congr 1
    ring
  have hlogpow : (Real.log (x : ℝ) ^ 100) ^ 2 *
      Real.log (x : ℝ) ^ 200 = Real.log (x : ℝ) ^ 400 := by
    ring
  have hpowTwo : ((2 : ℝ) ^ l) ^ 2 = (2 : ℝ) ^ (2 * l) := by
    rw [← pow_mul]
    congr 1
    omega
  unfold lemma6Equation20HFirstScale lemma6DyadicModulusScale
    lemma6PairDyadicScale
  rw [div_eq_mul_inv, mul_inv_rev, mul_pow, hxpow]
  calc
    ((2 : ℝ) ^ l) ^ 2 * (Real.log (x : ℝ) ^ 100) ^ 2 *
          ((x : ℝ) ^ (-(13 : ℝ) / 30) * ((2 : ℝ) ^ k)⁻¹) *
          Real.log (x : ℝ) ^ 200 * lemma6ExceptionalFactorAt x l =
        (((2 : ℝ) ^ l) ^ 2 * ((2 : ℝ) ^ k)⁻¹) *
          (x : ℝ) ^ (-(13 : ℝ) / 30) *
          ((Real.log (x : ℝ) ^ 100) ^ 2 *
            Real.log (x : ℝ) ^ 200) *
          lemma6ExceptionalFactorAt x l := by
      ring
    _ = (2 : ℝ) ^ (2 * l - k) *
          (x : ℝ) ^ (-(13 : ℝ) / 30) *
          (Real.log (x : ℝ)) ^ 400 *
          lemma6ExceptionalFactorAt x l := by
      rw [hpowTwo, htwoPow, hlogpow]

end Chen
