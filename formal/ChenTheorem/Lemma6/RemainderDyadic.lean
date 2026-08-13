/-
Dyadic assembly of the finite `C_H` polynomial in equation (14).

`RemainderConnection.lean` identifies the exact finite polynomial supported
on `H < n ≤ H²`; `MollifierLargeSieve.lean` estimates one interval
`M < n ≤ 2M`.  This file supplies the missing finite partition and the
Cauchy--Schwarz loss incurred when those intervals are put back together.
-/
import ChenTheorem.Lemma6.RemainderConnection

open scoped Classical

namespace Chen

/-- The `i`-th dyadic interval above `H`. -/
def lemma6RemainderDyadicBlock (H i : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ i * H) (2 ^ (i + 1) * H)

/-- There are enough blocks to cover `H < n ≤ H²`. -/
def lemma6RemainderDyadicIndices (H : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 H + 1)

theorem lemma6RemainderDyadicBlocks_pairwiseDisjoint (H : ℕ) :
    Set.PairwiseDisjoint (lemma6RemainderDyadicIndices H)
      (lemma6RemainderDyadicBlock H) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc] at hni hnj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega

/-- Every integer in the support interval of `C_H` belongs to one of the
dyadic blocks above `H`. -/
theorem lemma6RemainderSupport_subset_dyadicBlocks
    {H : ℕ} (hH : 1 ≤ H) :
    Finset.Ioc H (H * H) ⊆
      (lemma6RemainderDyadicIndices H).biUnion
        (lemma6RemainderDyadicBlock H) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_biUnion]
  refine ⟨Nat.log 2 ((n - 1) / H), ?_, ?_⟩
  · rw [lemma6RemainderDyadicIndices, Finset.mem_range,
      Nat.lt_succ_iff]
    apply Nat.log_mono_right
    apply (Nat.div_le_iff_le_mul (by omega : 0 < H)).2
    omega
  · rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc]
    constructor
    · have hr : 0 < (n - 1) / H := Nat.div_pos (by omega) (by omega)
      have hp := Nat.pow_log_le_self 2 hr.ne'
      have hmul : 2 ^ Nat.log 2 ((n - 1) / H) * H ≤ n - 1 := by
        calc
          2 ^ Nat.log 2 ((n - 1) / H) * H ≤
              ((n - 1) / H) * H :=
            Nat.mul_le_mul_right H hp
          _ ≤ n - 1 := Nat.div_mul_le_self _ _
      omega
    · have hp : (n - 1) / H <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
      have hmul : n - 1 <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) * H :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < H)).mp hp
      omega

/-- The summand in equation (14), normalized for the character large
sieve. -/
noncomputable def lemma6RemainderDyadicTerm
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  ((lemma6MollifierCoeff H n : ℂ) * lemma6RemainderPhase s n /
      (n : ℂ)) * χ n

theorem lemma6RemainderDyadicTerm_eq_zero_of_sq_lt
    {q H n : ℕ} (hH : 1 ≤ H) (hn : H * H < n) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6RemainderDyadicTerm H s χ n = 0 := by
  unfold lemma6RemainderDyadicTerm
  rw [lemma6MollifierCoeff_eq_zero_of_sq_lt hH hn]
  simp

/-- The dyadic blocks may extend beyond `H²`, but `C_H` vanishes there;
their sum is therefore exactly the finite remainder polynomial. -/
theorem lemma6MollifierRemainderPolynomial_eq_sum_dyadic
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s) =
      ∑ i ∈ lemma6RemainderDyadicIndices H,
        ∑ n ∈ lemma6RemainderDyadicBlock H i,
          lemma6RemainderDyadicTerm H s χ n := by
  rw [lemma6MollifierRemainderPolynomial_eq_largeSieve_sum hH]
  let U := (lemma6RemainderDyadicIndices H).biUnion
    (lemma6RemainderDyadicBlock H)
  have hsubset : Finset.Ioc H (H * H) ⊆ U := by
    simpa only [U] using lemma6RemainderSupport_subset_dyadicBlocks hH
  change (∑ n ∈ Finset.Ioc H (H * H),
      lemma6RemainderDyadicTerm H s χ n) = _
  calc
    (∑ n ∈ Finset.Ioc H (H * H),
        lemma6RemainderDyadicTerm H s χ n) =
        ∑ n ∈ U, lemma6RemainderDyadicTerm H s χ n := by
      apply Finset.sum_subset hsubset
      intro n hnU hnNot
      have hnH : H < n := by
        change n ∈ (lemma6RemainderDyadicIndices H).biUnion
          (lemma6RemainderDyadicBlock H) at hnU
        rw [Finset.mem_biUnion] at hnU
        obtain ⟨i, _hi, hni⟩ := hnU
        rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc] at hni
        have hpow : H ≤ 2 ^ i * H := by
          have hone : 1 ≤ (2 : ℕ) ^ i := one_le_pow₀ (by norm_num)
          simpa only [one_mul] using Nat.mul_le_mul_right H hone
        omega
      have hnHH : H * H < n := by
        by_contra h
        exact hnNot (Finset.mem_Ioc.mpr ⟨hnH, le_of_not_gt h⟩)
      exact lemma6RemainderDyadicTerm_eq_zero_of_sq_lt hH hnHH s χ
    _ = ∑ i ∈ lemma6RemainderDyadicIndices H,
          ∑ n ∈ lemma6RemainderDyadicBlock H i,
            lemma6RemainderDyadicTerm H s χ n :=
      Finset.sum_biUnion (lemma6RemainderDyadicBlocks_pairwiseDisjoint H)

/-- Finite Cauchy--Schwarz for reconstructing the remainder polynomial
from its dyadic pieces.  Its cardinal factor is the paper's logarithmic
loss in the display preceding equation (14). -/
theorem norm_lemma6MollifierRemainderPolynomial_sq_le_sum_dyadic
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ ^ 2 ≤
      (lemma6RemainderDyadicIndices H).card *
        ∑ i ∈ lemma6RemainderDyadicIndices H,
          ‖∑ n ∈ lemma6RemainderDyadicBlock H i,
            lemma6RemainderDyadicTerm H s χ n‖ ^ 2 := by
  rw [lemma6MollifierRemainderPolynomial_eq_sum_dyadic hH]
  let b : ℕ → ℂ := fun i =>
    ∑ n ∈ lemma6RemainderDyadicBlock H i,
      lemma6RemainderDyadicTerm H s χ n
  change ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ^ 2 ≤ _
  have htriangle : ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ≤
      ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ :=
    norm_sum_le _ _
  calc
    ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ^ 2 ≤
        (∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ i ∈ lemma6RemainderDyadicIndices H, (1 : ℝ) ^ 2) *
          ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ ^ 2 := by
      simpa only [one_mul] using
        (Finset.sum_mul_sq_le_sq_mul_sq
          (lemma6RemainderDyadicIndices H)
          (fun _ => (1 : ℝ)) (fun i => ‖b i‖))
    _ = (lemma6RemainderDyadicIndices H).card *
          ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ ^ 2 := by
      simp

theorem lemma6RemainderDyadicBlock_eq_Ioc_double (H i : ℕ) :
    lemma6RemainderDyadicBlock H i =
      Finset.Ioc (2 ^ i * H) (2 ^ i * H + 2 ^ i * H) := by
  unfold lemma6RemainderDyadicBlock
  congr 1
  rw [pow_succ]
  ring

/-- The finite `C_H` part of equation (14), after summing the dyadic
large-sieve estimate over all occupied `n`-blocks.  The right side is kept
as the exact finite dyadic sum; the following scalar step turns it into
Chen's `(Q/H + 1/D) (log x)^5` expression. -/
theorem lemma6_mollifier_remainder_large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 ≤ s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖lemma6MollifierRemainderPolynomial H
                (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
          C * (lemma6RemainderDyadicIndices H).card *
            ∑ i ∈ lemma6RemainderDyadicIndices H,
              ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
                (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_large_sieve_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H s hD hDQ hH hs
  let J := lemma6RemainderDyadicIndices H
  let B : (i q : ℕ) → DirichletCharacter ℂ q → ℝ := fun i q χ =>
    ‖∑ n ∈ lemma6RemainderDyadicBlock H i,
      lemma6RemainderDyadicTerm H s χ n‖ ^ 2
  have hpoint (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ‖lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s)‖ ^ 2 ≤
        J.card * ∑ i ∈ J, B i q χ := by
    simpa only [J, B] using
      norm_lemma6MollifierRemainderPolynomial_sq_le_sum_dyadic hH s χ
  have hblocks : ∀ i ∈ J,
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            B i q χ else 0) ≤
        C * ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
    intro i hi
    have hM : 1 ≤ 2 ^ i * H := by
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.one_le_iff_ne_zero.mp hH))
    have hphase : ∀ n ∈ Finset.Ioc (2 ^ i * H)
        (2 ^ i * H + 2 ^ i * H), ‖lemma6RemainderPhase s n‖ ≤ 1 := by
      intro n hn
      exact norm_lemma6RemainderPhase_le_one hs
        (hM.trans (Finset.mem_Ioc.mp hn).1.le)
    have hb := hlarge D Q (2 ^ i * H) H
      (lemma6RemainderPhase s) hD hDQ hM hphase
    simpa only [B, lemma6RemainderDyadicTerm,
      lemma6RemainderDyadicBlock_eq_Ioc_double] using hb
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma6MollifierRemainderPolynomial H
            (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          J.card * ∑ i ∈ J, B i q χ else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          split_ifs
          · exact hpoint q χ
          · exact le_rfl
        · positivity
    _ = J.card * ∑ i ∈ J,
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            B i q χ else 0) := by
      simp only [mul_ite, mul_zero, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp
    _ ≤ J.card * ∑ i ∈ J,
        C * ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
      gcongr with i hi
      exact hblocks i hi
    _ = C * J.card * ∑ i ∈ J,
        ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem card_lemma6RemainderDyadicIndices (H : ℕ) :
    (lemma6RemainderDyadicIndices H).card = Nat.log 2 H + 1 := by
  simp [lemma6RemainderDyadicIndices]

theorem lemma6RemainderDyadicBlock_top_le_sq
    {H i : ℕ} (hH : 1 ≤ H)
    (hi : i ∈ lemma6RemainderDyadicIndices H) :
    2 ^ i * H + 2 ^ i * H ≤ 2 * H * H := by
  have hiLog : i ≤ Nat.log 2 H := by
    simpa only [lemma6RemainderDyadicIndices, Finset.mem_range,
      Nat.lt_succ_iff] using hi
  have hpowLog : (2 : ℕ) ^ Nat.log 2 H ≤ H :=
    Nat.pow_log_le_self 2 (by omega)
  have hpow : (2 : ℕ) ^ i ≤ H :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hiLog).trans hpowLog
  nlinarith

theorem lemma6RemainderDyadic_log_le_log_sq
    {H i : ℕ} (hH : 1 ≤ H)
    (hi : i ∈ lemma6RemainderDyadicIndices H) :
    Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ) ≤
      Real.log ((2 * H * H : ℕ) : ℝ) := by
  have htop := lemma6RemainderDyadicBlock_top_le_sq hH hi
  have hleft : (0 : ℝ) < (2 ^ i * H + 2 ^ i * H : ℕ) := by
    exact_mod_cast (show 0 < 2 ^ i * H + 2 ^ i * H by
      have : 0 < H := by omega
      positivity)
  have hright : (0 : ℝ) < (2 * H * H : ℕ) := by
    exact_mod_cast (show 0 < 2 * H * H by positivity)
  exact Real.strictMonoOn_log.monotoneOn hleft
    hright (by exact_mod_cast htop)

theorem lemma6RemainderDyadic_inv_sum_le_two_div
    {H : ℕ} (hH : 1 ≤ H) :
    ∑ i ∈ lemma6RemainderDyadicIndices H,
        ((2 ^ i * H : ℕ) : ℝ)⁻¹ ≤ 2 / H := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  calc
    ∑ i ∈ lemma6RemainderDyadicIndices H,
        ((2 ^ i * H : ℕ) : ℝ)⁻¹ =
      (H : ℝ)⁻¹ * ∑ i ∈ Finset.range (Nat.log 2 H + 1),
        (1 / (2 : ℝ)) ^ i := by
      unfold lemma6RemainderDyadicIndices
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      rw [mul_inv, div_pow]
      norm_num
      ring
    _ ≤ (H : ℝ)⁻¹ * 2 := by
      apply mul_le_mul_of_nonneg_left
        (sum_geometric_two_le (Nat.log 2 H + 1))
      positivity
    _ = 2 / H := by
      rw [div_eq_mul_inv]
      ring

/-- Scalar form of the polynomial part of equation (14).  It displays
exactly the two logarithmic losses: one from Cauchy--Schwarz and one from
summing the `D⁻¹` contribution over the dyadic blocks. -/
theorem lemma6_mollifier_remainder_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 ≤ s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖lemma6MollifierRemainderPolynomial H
                (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
          C * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_remainder_large_sieve_dyadic with
    ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H s hD hDQ hH hs
  have hlog0 : 0 ≤ Real.log ((2 * H * H : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * H * H by nlinarith)
  have hsum :
      ∑ i ∈ lemma6RemainderDyadicIndices H,
          ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
            (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 ≤
        (2 * (Q : ℝ) / H +
          (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
          (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
    calc
      _ ≤ ∑ i ∈ lemma6RemainderDyadicIndices H,
          ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        have hfactor : 0 ≤
            (Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by
              have hpos : (0 : ℝ) <
                  (2 ^ i * H + 2 ^ i * H : ℕ) := by
                exact_mod_cast (show 0 < 2 ^ i * H + 2 ^ i * H by
                  have : 0 < H := by omega
                  nlinarith [show 0 < (2 : ℕ) ^ i by exact pow_pos (by norm_num) _])
              exact Real.log_nonneg (by
                exact_mod_cast (show 1 ≤ 2 ^ i * H + 2 ^ i * H by
                  have : 0 < H := by omega
                  nlinarith [show 0 < (2 : ℕ) ^ i by exact pow_pos (by norm_num) _])))
            (lemma6RemainderDyadic_log_le_log_sq hH hi) 3)
          hfactor
      _ = ((Q : ℝ) *
            ∑ i ∈ lemma6RemainderDyadicIndices H,
              ((2 ^ i * H : ℕ) : ℝ)⁻¹ +
          (lemma6RemainderDyadicIndices H).card * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (Q : ℝ) / H +
          (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        rw [card_lemma6RemainderDyadicIndices]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlog0 3)
        have hQ0 : 0 ≤ (Q : ℝ) := by positivity
        calc
          (Q : ℝ) * ∑ i ∈ lemma6RemainderDyadicIndices H,
                ((2 ^ i * H : ℕ) : ℝ)⁻¹ +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ ≤
            (Q : ℝ) * (2 / H) +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ := by
                gcongr
                exact lemma6RemainderDyadic_inv_sum_le_two_div hH
          _ = 2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ := by ring
          _ = 2 * (Q : ℝ) / H +
              ((Nat.log 2 H : ℝ) + 1) * (D : ℝ)⁻¹ := by
            norm_num only [Nat.cast_add, Nat.cast_one]
      _ = _ := by norm_num only [Nat.cast_add, Nat.cast_one]
  exact (hlarge D Q H s hD hDQ hH hs).trans <| by
    rw [card_lemma6RemainderDyadicIndices]
    have hcard0 : (0 : ℝ) ≤ (Nat.log 2 H + 1 : ℕ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hC.le hcard0)
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

end Chen
