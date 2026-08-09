/-
Dyadic conductor bookkeeping for equation (13) in the proof of Lemma 6.

The analytic fourth-moment bound is stated on `lemma6ModulusBlock x l`.
This file proves that the large squarefree conductors occurring in `N_m`
are covered by exactly one such positive block.
-/
import ChenTheorem.Lemma6.FourthMoment
import ChenTheorem.Lemma6.ExceptionalWeight

open Real Filter
open scoped Classical

namespace Chen

/-- The real upper endpoint of the `l`-th dyadic modulus block. -/
noncomputable def lemma6DyadicModulusScale (x l : ℕ) : ℝ :=
  (2 : ℝ) ^ l * (Real.log x) ^ 100

/-- The exceptional factor `I_{l,x}` appearing after equation (18). -/
noncomputable def lemma6ExceptionalFactorAt (x l : ℕ) : ℝ :=
  lemma6ExceptionalFactor (lemma6DyadicModulusScale x l)

/-- Eventually the base scale `(log x)^100` is beyond the range where
the monotonic exceptional-factor envelope is valid. -/
theorem eventually_exp_exp_one_le_log_pow_hundred :
    ∀ᶠ x : ℕ in atTop,
      Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100 := by
  have hlog :
      Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually
    (eventually_ge_atTop (Real.exp (Real.exp 1)))
  filter_upwards [hlarge] with x hx
  have hbase : 1 ≤ Real.log (x : ℝ) := by
    exact (Real.one_le_exp (Real.exp_pos 1).le).trans hx
  calc
    Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) := hx
    _ = Real.log (x : ℝ) ^ 1 := by rw [pow_one]
    _ ≤ Real.log (x : ℝ) ^ 100 :=
      pow_le_pow_right₀ hbase (by norm_num)

/-- Equation (18), in the pointwise squared form actually used on a
dyadic modulus block in equations (19) and (20). -/
theorem lemma6_equation18_sq_le_on_modulusBlock
    {x l d : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hd : d ∈ lemma6ModulusBlock x l) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      lemma6ExceptionalFactorAt x l := by
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) :=
    one_le_pow₀ (by norm_num)
  have hlogpow : 0 ≤ Real.log (x : ℝ) ^ 100 :=
    hxlarge.trans' (Real.exp_pos _).le
  have hlower : Real.exp (Real.exp 1) ≤
      (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 := by
    calc
      Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100 := hxlarge
      _ = 1 * Real.log (x : ℝ) ^ 100 := by rw [one_mul]
      _ ≤ (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 :=
        mul_le_mul_of_nonneg_right hpow hlogpow
  have hdlarge : Real.exp (Real.exp 1) < (d : ℝ) :=
    hlower.trans_lt hddata.2.2.1
  have hd2 : 2 ≤ d := by
    have htwo : (2 : ℝ) < Real.exp (Real.exp 1) := by
      exact Real.exp_one_gt_two.trans
        (Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr zero_lt_one))
    exact_mod_cast (htwo.trans hdlarge).le
  have hμ : ArithmeticFunction.moebius d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hddata.2.1
  exact lemma6_equation18_sq_le_exceptionalFactor hμ hd2 hdlarge
    hddata.2.2.2

/-- For all sufficiently large `x`, the equation-(18) exceptional factor
uniformly controls every modulus in every dyadic block. -/
theorem eventually_lemma6_equation18_sq_le_on_modulusBlock :
    ∀ᶠ x : ℕ in atTop, ∀ l d : ℕ,
      d ∈ lemma6ModulusBlock x l →
        ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
          lemma6ExceptionalFactorAt x l := by
  filter_upwards [eventually_exp_exp_one_le_log_pow_hundred] with x hx
  intro l d hd
  exact lemma6_equation18_sq_le_on_modulusBlock hx hd

/-- Weighted Cauchy--Schwarz after equation (17), with equation (18)
already absorbed uniformly over the modulus block.  The auxiliary index
type can include both a modulus and a primitive character. -/
theorem lemma6_weighted_cauchy_on_modulusBlock
    {ι : Type*} (s : Finset ι) (modulus : ι → ℕ)
    (w f g : ι → ℝ) {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hmodulus : ∀ i ∈ s, modulus i ∈ lemma6ModulusBlock x l)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s,
        w i * (3 : ℝ) ^ distinctPrimeFactors (modulus i) * f i * g i) ^ 2 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ s, w i * f i ^ 2) *
        ∑ i ∈ s, w i * g i ^ 2 := by
  apply weighted_cauchy_sq_of_sq_le
  · exact hw
  · exact (lemma6ExceptionalFactor_pos _).le
  · intro i hi
    exact lemma6_equation18_sq_le_on_modulusBlock hxlarge
      (hmodulus i hi)

/-- The `2,4,4` Hölder estimate used for the `B` integral in equation
(19), again with equation (18) already absorbed into `I_{l,x}`. -/
theorem lemma6_weighted_holder_244_on_modulusBlock
    {ι : Type*} (s : Finset ι) (modulus : ι → ℕ)
    (w f g h : ι → ℝ) {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hmodulus : ∀ i ∈ s, modulus i ∈ lemma6ModulusBlock x l)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) :
    (∑ i ∈ s,
        w i * (3 : ℝ) ^ distinctPrimeFactors (modulus i) *
          f i * g i * h i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ s, w i * f i ^ 2) ^ 2 *
        (∑ i ∈ s, w i * g i ^ 4) *
          ∑ i ∈ s, w i * h i ^ 4 := by
  apply weighted_holder_244_pow_four_of_sq_le
  · exact hw
  · intro i hi
    positivity
  · exact hf
  · exact hg
  · exact hh
  · exact (lemma6ExceptionalFactor_pos _).le
  · intro i hi
    exact lemma6_equation18_sq_le_on_modulusBlock hxlarge
      (hmodulus i hi)

/-- Every squarefree conductor above `(log x)^100` and at most `x` belongs
to a positive dyadic modulus block. -/
theorem exists_mem_lemma6ModulusBlock
    {x d : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hdlarge : Real.log (x : ℝ) ^ 100 < (d : ℝ))
    (hdsq : Squarefree d) (hdx : d ≤ x) :
    ∃ l : ℕ, 1 ≤ l ∧ d ∈ lemma6ModulusBlock x l := by
  let T : ℝ := Real.log (x : ℝ) ^ 100
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hr : (1 : ℝ) < (d : ℝ) / T := by
    rw [lt_div_iff₀ hTpos]
    simpa only [one_mul, T] using hdlarge
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_nat_pow_near hr.le (by norm_num : (1 : ℝ) < 2)
  have hdmem : d ∈ Finset.range (x + 1) :=
    Finset.mem_range.mpr (by omega)
  by_cases heq : (2 : ℝ) ^ n = (d : ℝ) / T
  · have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      subst n
      norm_num at heq
      linarith
    refine ⟨n, by omega, ?_⟩
    rw [lemma6ModulusBlock, Finset.mem_filter]
    refine ⟨hdmem, hdsq, ?_, ?_⟩
    · have hpow : (2 : ℝ) ^ (n - 1) < (2 : ℝ) ^ n :=
        pow_lt_pow_right₀ (by norm_num) (Nat.sub_one_lt hnpos.ne')
      calc
        (2 : ℝ) ^ (n - 1) * Real.log (x : ℝ) ^ 100 =
            (2 : ℝ) ^ (n - 1) * T := by rfl
        _ < (2 : ℝ) ^ n * T := mul_lt_mul_of_pos_right hpow hTpos
        _ = ((d : ℝ) / T) * T := by rw [heq]
        _ = d := div_mul_cancel₀ _ hTpos.ne'
    · calc
        (d : ℝ) = ((d : ℝ) / T) * T :=
          (div_mul_cancel₀ _ hTpos.ne').symm
        _ = (2 : ℝ) ^ n * T := by rw [heq]
        _ ≤ (2 : ℝ) ^ n * Real.log (x : ℝ) ^ 100 := by rfl
  · refine ⟨n + 1, by omega, ?_⟩
    rw [lemma6ModulusBlock, Finset.mem_filter]
    refine ⟨hdmem, hdsq, ?_, ?_⟩
    · have hnlow' : (2 : ℝ) ^ n < (d : ℝ) / T :=
        lt_of_le_of_ne hnlow heq
      calc
        (2 : ℝ) ^ (n + 1 - 1) * Real.log (x : ℝ) ^ 100 =
            (2 : ℝ) ^ n * T := by congr 2
        _ < ((d : ℝ) / T) * T :=
          mul_lt_mul_of_pos_right hnlow' hTpos
        _ = d := div_mul_cancel₀ _ hTpos.ne'
    · calc
        (d : ℝ) = ((d : ℝ) / T) * T :=
          (div_mul_cancel₀ _ hTpos.ne').symm
        _ ≤ (2 : ℝ) ^ (n + 1) * T :=
          (mul_lt_mul_of_pos_right hnup hTpos).le
        _ = (2 : ℝ) ^ (n + 1) * Real.log (x : ℝ) ^ 100 := by rfl

/-- The half-open dyadic convention makes the block index unique. -/
theorem lemma6ModulusBlock_index_unique
    {x d l k : ℕ}
    (hdl : d ∈ lemma6ModulusBlock x l)
    (hdk : d ∈ lemma6ModulusBlock x k) :
    l = k := by
  have hldata := hdl
  have hkdata := hdk
  rw [lemma6ModulusBlock, Finset.mem_filter] at hldata hkdata
  rcases lt_trichotomy l k with hlk | rfl | hkl
  · have hexp : l ≤ k - 1 := by omega
    have hpow : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ (k - 1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul : (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ (k - 1) * Real.log (x : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    linarith [hldata.2.2.2, hkdata.2.2.1]
  · rfl
  · have hexp : k ≤ l - 1 := by omega
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (l - 1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul : (2 : ℝ) ^ k * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    linarith [hkdata.2.2.2, hldata.2.2.1]

/-- Canonical index of a modulus block.  The fallback value is irrelevant
outside the union of the blocks. -/
noncomputable def lemma6ModulusBlockIndex (x d : ℕ) : ℕ :=
  if h : ∃ l : ℕ, d ∈ lemma6ModulusBlock x l then Nat.find h else 0

theorem lemma6ModulusBlockIndex_mem
    {x d : ℕ} (h : ∃ l : ℕ, d ∈ lemma6ModulusBlock x l) :
    d ∈ lemma6ModulusBlock x (lemma6ModulusBlockIndex x d) := by
  rw [lemma6ModulusBlockIndex, dif_pos h]
  exact Nat.find_spec h

/-- On an actual block, the canonical index is that block's index. -/
theorem lemma6ModulusBlockIndex_eq
    {x d l : ℕ} (hd : d ∈ lemma6ModulusBlock x l) :
    lemma6ModulusBlockIndex x d = l :=
  lemma6ModulusBlock_index_unique
    (lemma6ModulusBlockIndex_mem ⟨l, hd⟩) hd

/-- The `k`-th dyadic prime-pair block in equation (13). -/
noncomputable def lemma6PairBlock (x k : ℕ) : Finset (ℕ × ℕ) :=
  (chenPairs x).filter fun q =>
    (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30) <
        (q.1 * q.2 : ℕ) ∧
      ((q.1 * q.2 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (k + 1) * (x : ℝ) ^ ((13 : ℝ) / 30)

/-- Every Chen prime pair lies above the initial product scale
`x^(13/30)`. -/
theorem chenPair_product_lower
    {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    (x : ℝ) ^ ((13 : ℝ) / 30) < (q.1 * q.2 : ℕ) := by
  have hqdata := (Finset.mem_filter.mp hq).2
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  calc
    (x : ℝ) ^ ((13 : ℝ) / 30) =
        (x : ℝ) ^ ((1 : ℝ) / 10) *
          (x : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    _ < (q.1 : ℝ) * q.2 := by
      exact mul_lt_mul hqdata.2.2.1 hqdata.2.2.2.2.1.le
        (Real.rpow_pos_of_pos hxpos _) (by positivity)
    _ = (q.1 * q.2 : ℕ) := by norm_num

/-- Every Chen prime pair belongs to a pair-product dyadic block. -/
theorem exists_mem_lemma6PairBlock
    {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    ∃ k : ℕ, q ∈ lemma6PairBlock x k := by
  let T : ℝ := (x : ℝ) ^ ((13 : ℝ) / 30)
  let p : ℝ := (q.1 * q.2 : ℕ)
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hpT : T < p := by
    simpa only [T, p] using chenPair_product_lower hx hq
  have hr : (1 : ℝ) < p / T := by
    rw [lt_div_iff₀ hTpos]
    simpa only [one_mul] using hpT
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_nat_pow_near hr.le (by norm_num : (1 : ℝ) < 2)
  by_cases heq : (2 : ℝ) ^ n = p / T
  · have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      subst n
      norm_num at heq
      linarith
    refine ⟨n - 1, ?_⟩
    rw [lemma6PairBlock, Finset.mem_filter]
    refine ⟨hq, ?_, ?_⟩
    · have hpow : (2 : ℝ) ^ (n - 1) < (2 : ℝ) ^ n :=
        pow_lt_pow_right₀ (by norm_num) (Nat.sub_one_lt hnpos.ne')
      change (2 : ℝ) ^ (n - 1) * T < p
      calc
        (2 : ℝ) ^ (n - 1) * T < (2 : ℝ) ^ n * T :=
          mul_lt_mul_of_pos_right hpow hTpos
        _ = (p / T) * T := by rw [heq]
        _ = p := div_mul_cancel₀ _ hTpos.ne'
    · change p ≤ (2 : ℝ) ^ (n - 1 + 1) * T
      calc
        p = (p / T) * T := (div_mul_cancel₀ _ hTpos.ne').symm
        _ = (2 : ℝ) ^ n * T := by rw [heq]
        _ ≤ (2 : ℝ) ^ (n - 1 + 1) * T := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  · refine ⟨n, ?_⟩
    rw [lemma6PairBlock, Finset.mem_filter]
    refine ⟨hq, ?_, ?_⟩
    · have hnlow' : (2 : ℝ) ^ n < p / T :=
        lt_of_le_of_ne hnlow heq
      change (2 : ℝ) ^ n * T < p
      calc
        (2 : ℝ) ^ n * T < (p / T) * T :=
          mul_lt_mul_of_pos_right hnlow' hTpos
        _ = p := div_mul_cancel₀ _ hTpos.ne'
    · change p ≤ (2 : ℝ) ^ (n + 1) * T
      calc
        p = (p / T) * T := (div_mul_cancel₀ _ hTpos.ne').symm
        _ ≤ (2 : ℝ) ^ (n + 1) * T :=
          (mul_lt_mul_of_pos_right hnup hTpos).le

/-- Pair-product dyadic blocks are disjoint. -/
theorem lemma6PairBlock_index_unique
    {x : ℕ} {q : ℕ × ℕ} {k j : ℕ}
    (hqk : q ∈ lemma6PairBlock x k)
    (hqj : q ∈ lemma6PairBlock x j) :
    k = j := by
  have hkdata := (Finset.mem_filter.mp hqk).2
  have hjdata := (Finset.mem_filter.mp hqj).2
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · have hexp : k + 1 ≤ j := by omega
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul :
        (2 : ℝ) ^ (k + 1) * (x : ℝ) ^ ((13 : ℝ) / 30) ≤
          (2 : ℝ) ^ j * (x : ℝ) ^ ((13 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (by positivity) _)
    linarith [hkdata.2, hjdata.1]
  · rfl
  · have hexp : j + 1 ≤ k := by omega
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul :
        (2 : ℝ) ^ (j + 1) * (x : ℝ) ^ ((13 : ℝ) / 30) ≤
          (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (by positivity) _)
    linarith [hjdata.2, hkdata.1]

/-- Canonical `k`-index of a Chen prime pair. -/
noncomputable def lemma6PairBlockIndex (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  if h : ∃ k : ℕ, q ∈ lemma6PairBlock x k then Nat.find h else 0

theorem lemma6PairBlockIndex_mem
    {x : ℕ} {q : ℕ × ℕ}
    (h : ∃ k : ℕ, q ∈ lemma6PairBlock x k) :
    q ∈ lemma6PairBlock x (lemma6PairBlockIndex x q) := by
  rw [lemma6PairBlockIndex, dif_pos h]
  exact Nat.find_spec h

theorem lemma6PairBlockIndex_eq
    {x k : ℕ} {q : ℕ × ℕ} (hq : q ∈ lemma6PairBlock x k) :
    lemma6PairBlockIndex x q = k :=
  lemma6PairBlock_index_unique (lemma6PairBlockIndex_mem ⟨k, hq⟩) hq

/-- Comparison between the integer binary logarithm used to count dyadic
blocks and the real logarithm used in the analytic estimates. -/
theorem natLog_two_cast_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hn0 : n ≠ 0 := by omega
  have hpowNat : (2 : ℕ) ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa [mul_comm] using hlog

end Chen
