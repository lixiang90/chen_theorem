/-
Arithmetic coefficient estimates used in equation (12) of Lemma 6.

The proof below is slightly stronger than the estimate quoted by Chen.  On
squarefree integers, `3^ν(d) / d` is dominated by the third Dirichlet
convolution power of `1 / n`; its partial sums are therefore bounded by the
cube of the harmonic sum.  The remaining factor `d / φ(d)` costs one
logarithm.
-/
import ChenTheorem.Lemma5.Boundary.Analytic

open Finset Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The nonnegative sieve coefficient `|μ(d)| 3^ν(d) / φ(d)`. -/
noncomputable def lemma6TotientWeight (d : ℕ) : ℝ :=
  |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
    (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)

theorem lemma6TotientWeight_nonneg (d : ℕ) :
    0 ≤ lemma6TotientWeight d := by
  unfold lemma6TotientWeight
  positivity

/-- The sieve coefficient is multiplicative on coprime positive inputs. -/
theorem lemma6TotientWeight_mul {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    lemma6TotientWeight (a * b) =
      lemma6TotientWeight a * lemma6TotientWeight b := by
  unfold lemma6TotientWeight distinctPrimeFactors
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      hab.gcd_eq_one,
    Nat.primeFactors_mul ha hb,
    Finset.card_union_of_disjoint hab.disjoint_primeFactors,
    Nat.totient_mul hab]
  push_cast
  rw [abs_mul, pow_add]
  ring

/-- The corresponding coefficient with denominator `d`. -/
noncomputable def lemma6LinearWeight (d : ℕ) : ℝ :=
  |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
    (3 : ℝ) ^ distinctPrimeFactors d / (d : ℝ)

theorem lemma6LinearWeight_nonneg (d : ℕ) :
    0 ≤ lemma6LinearWeight d := by
  unfold lemma6LinearWeight
  positivity

private noncomputable def invNatTwist (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else f n / (n : ℝ)
  map_zero' := if_pos rfl

@[simp]
private theorem invNatTwist_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    invNatTwist f n = if n = 0 then 0 else f n / (n : ℝ) := rfl

private theorem invNatTwist_mul (f g : ArithmeticFunction ℝ) :
    invNatTwist (f * g) = invNatTwist f * invNatTwist g := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  change
    (if n = 0 then 0 else
      (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) / (n : ℝ)) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 = 0 then 0 else f p.1 / (p.1 : ℝ)) *
          (if p.2 = 0 then 0 else g p.2 / (p.2 : ℝ))
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
    have hp₁ : p.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hp₂ : p.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    simp only [hp₁, hp₂, if_false]
    rw [← hpdata.1]
    push_cast
    field_simp

private theorem partialSum_mul_le_mul
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (f * g) n ≤
      (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
  calc
    ∑ p ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter
        (fun p => p.1 * p.2 ≤ N), f p.1 * g p.2 ≤
        ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N,
          f p.1 * g p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp hnot
      exact mul_nonneg (hf p.1) (hg p.2)
    _ = (∑ n ∈ Finset.Ioc 0 N, f n) *
        ∑ n ∈ Finset.Ioc 0 N, g n := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

private theorem invNatTwist_zeta_nonneg (n : ℕ) :
    0 ≤ invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : n = 0
  · simp [invNatTwist, hn]
  · simp [invNatTwist, hn, ArithmeticFunction.zeta_apply]

private theorem sum_invNatTwist_zeta (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n =
      (harmonic N : ℝ) := by
  have hfin : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  rw [hfin, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  simp [invNatTwist, hnpos.ne', ArithmeticFunction.zeta_apply,
    Rat.cast_inv, Rat.cast_natCast]

private theorem sum_invNatTwist_zeta_cube_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) n ≤
      (harmonic N : ℝ) ^ 3 := by
  let z := invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hz : ∀ n, 0 ≤ z n := invNatTwist_zeta_nonneg
  have hzz : ∀ n, 0 ≤ (z * z) n := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hz p.1) (hz p.2)
  calc
    ∑ n ∈ Finset.Ioc 0 N, (z ^ 3) n =
        ∑ n ∈ Finset.Ioc 0 N, ((z * z) * z) n := by rw [pow_succ, pow_two]
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (z * z) n) *
        ∑ n ∈ Finset.Ioc 0 N, z n :=
      partialSum_mul_le_mul (z * z) z hzz hz N
    _ ≤ ((∑ n ∈ Finset.Ioc 0 N, z n) *
        ∑ n ∈ Finset.Ioc 0 N, z n) *
          ∑ n ∈ Finset.Ioc 0 N, z n := by
      apply mul_le_mul_of_nonneg_right
        (partialSum_mul_le_mul z z hz hz N)
      exact Finset.sum_nonneg fun n hn => hz n
    _ = (harmonic N : ℝ) ^ 3 := by
      rw [show ∑ n ∈ Finset.Ioc 0 N, z n = (harmonic N : ℝ) by
        exact sum_invNatTwist_zeta N]
      ring

private theorem zeta_cube_apply_squarefree_real {d : ℕ} (hd : Squarefree d) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      (3 : ℝ) ^ d.primeFactors.card := by
  have hnat :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) d =
        3 ^ d.primeFactors.card := by
    rw [show (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3 =
        ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta by
      have hz :
          (ArithmeticFunction.zeta : ArithmeticFunction ℕ) *
              ArithmeticFunction.zeta = ArithmeticFunction.sigma 0 := by
        simpa only [ArithmeticFunction.pow_zero_eq_zeta] using
          (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 0))
      rw [pow_succ, pow_two, hz]]
    rw [← ArithmeticFunction.isMultiplicative_sigma.prodPrimeFactors_add_of_squarefree
      ArithmeticFunction.isMultiplicative_zeta hd]
    rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hs := ArithmeticFunction.sigma_zero_apply_prime_pow
      (i := 1) hpprime
    norm_num at hs
    rw [ArithmeticFunction.add_apply, hs]
    simp [ArithmeticFunction.zeta_apply, hpprime.ne_zero]
  have hcoe :
      (↑((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) :
          ArithmeticFunction ℝ) =
        (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ) ^ 3 := by
    rw [pow_succ, pow_two, pow_succ, pow_two,
      ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_mul]
  rw [← hcoe]
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
  simpa only [ArithmeticFunction.natCoe_apply, Nat.cast_pow,
    Nat.cast_ofNat] using hcast

private theorem invNatTwist_zeta_cube_eq (d : ℕ) :
    invNatTwist ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 3) d =
      ((invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  congr 1
  rw [pow_succ, pow_two, invNatTwist_mul, invNatTwist_mul,
    pow_succ, pow_two]

private theorem invNatTwist_zeta_cube_nonneg (d : ℕ) :
    0 ≤ ((invNatTwist
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  let z := invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  change 0 ≤ (z ^ 3) d
  rw [pow_succ, pow_two, ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (invNatTwist_zeta_nonneg q.1)
      (invNatTwist_zeta_nonneg q.2)
  · exact invNatTwist_zeta_nonneg p.2

private theorem lemma6LinearWeight_le_cube (d : ℕ) :
    lemma6LinearWeight d ≤
      ((invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ^ 3) d := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    rw [← invNatTwist_zeta_cube_eq]
    unfold lemma6LinearWeight distinctPrimeFactors
    rw [invNatTwist_apply, if_neg hd0, zeta_cube_apply_squarefree_real hd]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs,
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
      norm_num
    rw [hmu, one_mul]
  · unfold lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
    exact invNatTwist_zeta_cube_nonneg d

/-- The linear-denominator sieve weights have a cubic harmonic bound. -/
theorem sum_sieveModuli_lemma6LinearWeight_le (x : ℕ) (ε : ℝ) :
    ∑ d ∈ sieveModuli x ε, lemma6LinearWeight d ≤
      (harmonic x : ℝ) ^ 3 := by
  let z := invNatTwist (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hsubset : sieveModuli x ε ⊆ Finset.Ioc 0 x := by
    intro d hd
    rw [sieveModuli, Finset.mem_filter] at hd
    rw [Finset.mem_Ioc]
    have hdrange : d < x + 1 := Finset.mem_range.mp hd.1
    exact ⟨by omega, by omega⟩
  calc
    ∑ d ∈ sieveModuli x ε, lemma6LinearWeight d ≤
        ∑ d ∈ sieveModuli x ε, (z ^ 3) d := by
      apply Finset.sum_le_sum
      intro d hd
      exact lemma6LinearWeight_le_cube d
    _ ≤ ∑ d ∈ Finset.Ioc 0 x, (z ^ 3) d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd hnot
      exact invNatTwist_zeta_cube_nonneg d
    _ ≤ (harmonic x : ℝ) ^ 3 := sum_invNatTwist_zeta_cube_le x

private theorem prod_le_card_succ_prod_sub_one
    (S : Finset ℕ) (hmin : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, p ≤ (S.card + 1) * ∏ p ∈ S, (p - 1) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
      by_cases hS : S = ∅
      · simp [hS]
      · let p := S.max' (Finset.nonempty_iff_ne_empty.mpr hS)
        have hpS : p ∈ S := Finset.max'_mem S _
        let T := S.erase p
        have hTsub : T ⊂ S := Finset.erase_ssubset hpS
        have hTmin : ∀ q ∈ T, 2 ≤ q := by
          intro q hq
          exact hmin q (Finset.mem_of_mem_erase hq)
        have hih := ih T hTsub hTmin
        have hp2 : 2 ≤ p := hmin p hpS
        have hsubset : S ⊆ Finset.Icc 2 p := by
          intro q hq
          exact Finset.mem_Icc.mpr
            ⟨hmin q hq, Finset.le_max' S q hq⟩
        have hcard : S.card + 1 ≤ p := by
          have hc := Finset.card_le_card hsubset
          rw [Nat.card_Icc] at hc
          omega
        have hcardT : T.card + 1 = S.card := by
          dsimp only [T]
          exact Finset.card_erase_add_one hpS
        have hcoef : p * (T.card + 1) ≤ (S.card + 1) * (p - 1) := by
          rw [hcardT]
          have hpsub : p - 1 + 1 = p := by omega
          nlinarith
        calc
          ∏ q ∈ S, q = p * ∏ q ∈ T, q := by
            dsimp only [T]
            rw [← Finset.prod_erase_mul _ _ hpS]
            ring
          _ ≤ p * ((T.card + 1) * ∏ q ∈ T, (q - 1)) :=
            Nat.mul_le_mul_left p hih
          _ = (p * (T.card + 1)) * ∏ q ∈ T, (q - 1) := by ring
          _ ≤ ((S.card + 1) * (p - 1)) *
              ∏ q ∈ T, (q - 1) :=
            Nat.mul_le_mul_right _ hcoef
          _ = (S.card + 1) * ∏ q ∈ S, (q - 1) := by
            dsimp only [T]
            rw [← Finset.prod_erase_mul _ (fun q => q - 1) hpS]
            ring

theorem totient_ratio_le_card_succ {n : ℕ} (hn : Squarefree n) :
    (n : ℝ) / (Nat.totient n : ℝ) ≤
      (n.primeFactors.card + 1 : ℝ) := by
  have hprod := prod_le_card_succ_prod_sub_one n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  rw [Nat.prod_primeFactors_of_squarefree hn] at hprod
  have htotNat :
      Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self (Nat.pos_of_ne_zero hn.ne_zero), one_mul]
  rw [← htotNat] at hprod
  have htotpos : 0 < (Nat.totient n : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn.ne_zero)
  rw [div_le_iff₀ htotpos]
  exact_mod_cast hprod

theorem primeFactors_card_succ_le_log {n : ℕ}
    (hn : Squarefree n) (hn2 : 2 ≤ n) :
    (n.primeFactors.card + 1 : ℝ) ≤
      (2 / Real.log 2) * Real.log n := by
  let r := n.primeFactors.card
  have hpow : 2 ^ r ≤ n := by
    calc
      2 ^ r = ∏ _p ∈ n.primeFactors, 2 := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod
        · intro p hp
          omega
        · intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hlogmono : Real.log ((2 : ℝ) ^ r) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hpowpos)
      (Set.mem_Ioi.mpr (by positivity)) (by exact_mod_cast hpow)
  rw [Real.log_pow] at hlogmono
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity)) (by exact_mod_cast hn2)
  have hr : (r : ℝ) ≤ Real.log n / Real.log 2 := by
    exact (le_div_iff₀ hlog2).2 (by simpa [mul_comm] using hlogmono)
  have hone : (1 : ℝ) ≤ Real.log n / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogn)
  calc
    (r : ℝ) + 1 ≤
        Real.log n / Real.log 2 + Real.log n / Real.log 2 :=
      add_le_add hr hone
    _ = (2 / Real.log 2) * Real.log n := by ring

/-- A squarefree form of the elementary estimate
`1 / φ(n) ≪ log(n) / n`. -/
theorem inv_totient_le_log_div_self {n : ℕ}
    (hn : Squarefree n) (hn2 : 2 ≤ n) :
    (Nat.totient n : ℝ)⁻¹ ≤
      (2 / Real.log 2) * Real.log n / n := by
  have hratio := (totient_ratio_le_card_succ hn).trans
    (primeFactors_card_succ_le_log hn hn2)
  have hnpos : (0 : ℝ) < n := by positivity
  have htotpos : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [div_eq_mul_inv]
  calc
    (Nat.totient n : ℝ)⁻¹ =
        ((n : ℝ) / (Nat.totient n : ℝ)) * (n : ℝ)⁻¹ := by
      field_simp
    _ ≤ ((2 / Real.log 2) * Real.log n) * (n : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hratio (by positivity)

/-- On a squarefree modulus at least two, replacing `φ(d)` by `d` costs
one logarithm. -/
theorem lemma6TotientWeight_le_log_mul_linearWeight
    {x d : ℕ} (hd : d ∈ sieveModuli x ε) (hd2 : 2 ≤ d) :
    lemma6TotientWeight d ≤
      (2 / Real.log 2) * Real.log x * lemma6LinearWeight d := by
  by_cases hdsq : Squarefree d
  · have hdx : d ≤ x := by
      have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
      omega
    have hratio := (totient_ratio_le_card_succ hdsq).trans
      (primeFactors_card_succ_le_log hdsq hd2)
    have hlog : Real.log d ≤ Real.log x := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hdx)
    have hconst : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
    have hratio' : (d : ℝ) / (Nat.totient d : ℝ) ≤
        (2 / Real.log 2) * Real.log x :=
      hratio.trans (mul_le_mul_of_nonneg_left hlog hconst)
    have htotpos : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    unfold lemma6TotientWeight lemma6LinearWeight
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d * (Nat.totient d : ℝ)⁻¹ =
          ((d : ℝ) / (Nat.totient d : ℝ)) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        field_simp
      _ ≤ ((2 / Real.log 2) * Real.log x) *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right hratio'
        positivity
      _ = (2 / Real.log 2) * Real.log x *
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d * (d : ℝ)⁻¹) := by ring
  · unfold lemma6TotientWeight lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
    norm_num

/-- Summed form of the outer coefficient estimate in equation (12). -/
theorem sum_sieveModuli_lemma6TotientWeight_le
    {x : ℕ} (hx2 : 2 ≤ x) (ε : ℝ) :
    ∑ d ∈ sieveModuli x ε, lemma6TotientWeight d ≤
      1 + (2 / Real.log 2) * Real.log x * (harmonic x : ℝ) ^ 3 := by
  -- The exceptional modulus `d = 1` contributes exactly one.
  calc
    ∑ d ∈ sieveModuli x ε, lemma6TotientWeight d ≤
        1 + ∑ d ∈ (sieveModuli x ε).erase 1,
          lemma6TotientWeight d := by
      by_cases h1 : 1 ∈ sieveModuli x ε
      · rw [← Finset.add_sum_erase _ _ h1]
        simp [lemma6TotientWeight, distinctPrimeFactors]
      · rw [Finset.erase_eq_self.mpr h1]
        linarith
    _ ≤ 1 + ∑ d ∈ (sieveModuli x ε).erase 1,
          ((2 / Real.log 2) * Real.log x) * lemma6LinearWeight d := by
      gcongr with d hd
      exact lemma6TotientWeight_le_log_mul_linearWeight
        (Finset.mem_of_mem_erase hd) (by
          have hdne := Finset.ne_of_mem_erase hd
          have hdpos := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).2.1
          omega)
    _ ≤ 1 + ((2 / Real.log 2) * Real.log x) *
          ∑ d ∈ sieveModuli x ε, lemma6LinearWeight d := by
      rw [Finset.mul_sum]
      apply add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun d hd hnot => mul_nonneg (by
          have hx1 : 1 ≤ x := by omega
          have : (0 : ℝ) ≤ Real.log x :=
            Real.log_nonneg (by exact_mod_cast hx1)
          positivity) (lemma6LinearWeight_nonneg d)))
    _ ≤ 1 + (2 / Real.log 2) * Real.log x *
          (harmonic x : ℝ) ^ 3 := by
      gcongr
      exact sum_sieveModuli_lemma6LinearWeight_le x ε

end Chen
