/-
Assembly of the two inputs in Chen's Lemma 3: the large-sieve fourth
moment of the finite polynomial and the Pólya--Vinogradov truncation error.
-/
import ChenTheorem.Lemma3.Approximation

open Real
open scoped Classical

namespace Chen

/-- Chen's truncation length, regularized so it is uniformly positive. -/
noncomputable def lemma3Cutoff (Q : ℕ) (s : ℂ) : ℕ :=
  ⌈(Q : ℝ) * (1 + ‖s‖)⌉₊

theorem lemma3Cutoff_two_le {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q) :
    2 ≤ lemma3Cutoff Q s := by
  have hscale : (2 : ℝ) ≤ (Q : ℝ) * (1 + ‖s‖) := by
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [norm_nonneg s]
  have hceil := Nat.le_ceil ((Q : ℝ) * (1 + ‖s‖))
  unfold lemma3Cutoff
  exact_mod_cast hscale.trans hceil

theorem lemma3Cutoff_scale_le (Q : ℕ) (s : ℂ) :
    (Q : ℝ) * (1 + ‖s‖) ≤ lemma3Cutoff Q s := by
  unfold lemma3Cutoff
  exact Nat.le_ceil _

theorem lemma3Cutoff_le_two_mul {Q : ℕ} {s : ℂ} (hQ : 1 ≤ Q) :
    (lemma3Cutoff Q s : ℝ) ≤ 2 * (Q : ℝ) * (1 + ‖s‖) := by
  unfold lemma3Cutoff
  have hscale : (1 : ℝ) ≤ (Q : ℝ) * (1 + ‖s‖) := by
    have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [norm_nonneg s]
  have h := Nat.ceil_le_two_mul (by linarith : (2 : ℝ)⁻¹ ≤
    (Q : ℝ) * (1 + ‖s‖))
  nlinarith

/-- The cutoff cancels the square-root conductor loss in the
Pólya--Vinogradov remainder. -/
theorem sqrt_mul_lemma3Cutoff_rpow_le
    {q Q : ℕ} {s : ℂ} (hqQ : q ≤ Q) (hQ : 1 ≤ Q) :
    Real.sqrt q * (lemma3Cutoff Q s : ℝ) ^ ((-1 : ℝ) / 2) ≤
      (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by
  let N := lemma3Cutoff Q s
  let t : ℝ := ‖s‖
  have ht0 : 0 ≤ t := norm_nonneg s
  have htp : 0 < 1 + t := by positivity
  have hscale : (Q : ℝ) * (1 + t) ≤ N :=
    lemma3Cutoff_scale_le Q s
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hNpos : (0 : ℝ) < N :=
    (mul_pos hQpos htp).trans_le hscale
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hqQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqscale : (q : ℝ) * (1 + t) ≤ N :=
    (mul_le_mul_of_nonneg_right hqQr (by positivity)).trans hscale
  have hratio : (q : ℝ) * (N : ℝ)⁻¹ ≤ (1 + t)⁻¹ := by
    have hdiv : (q : ℝ) / (N : ℝ) ≤ (1 : ℝ) / (1 + t) :=
      (div_le_div_iff₀ hNpos htp).2 (by simpa using hqscale)
    simpa [div_eq_mul_inv] using hdiv
  have hNpow : ((N : ℝ) ^ ((-1 : ℝ) / 2)) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
    rw [Real.rpow_neg_one]
  have htpPow : ((1 + t) ^ ((-1 : ℝ) / 2)) ^ 2 = (1 + t)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htp.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hy0 : 0 ≤ Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2) := by positivity
  have hz0 : 0 ≤ (1 + t) ^ ((-1 : ℝ) / 2) := by positivity
  change Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2) ≤
    (1 + t) ^ ((-1 : ℝ) / 2)
  apply (sq_le_sq₀ hy0 hz0).1
  rw [mul_pow, Real.sq_sqrt (by positivity), hNpow, htpPow]
  exact hratio

/-- Pointwise truncation error after inserting the common cutoff. -/
theorem norm_LFunction_sub_lemma3Cutoff_le
    {q Q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hqQ : q ≤ Q)
    (hQ : 2 ≤ Q) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s -
        lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ≤
      12 * ‖s‖ * Real.log (2 * (Q : ℝ) * (1 + ‖s‖)) *
        (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by
  let N := lemma3Cutoff Q s
  let A : ℝ := 2 * (Q : ℝ) * (1 + ‖s‖)
  have hN2 : 2 ≤ N := lemma3Cutoff_two_le hQ
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (-s.re) ≤
      (N : ℝ) ^ ((-1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
  have hroot : Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2) ≤
      (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by
    simpa only [N] using sqrt_mul_lemma3Cutoff_rpow_le hqQ (show 1 ≤ Q by omega)
  have hqpos : (0 : ℝ) < 2 * q := by positivity
  have hqA : (2 * (q : ℝ)) ≤ A := by
    dsimp only [A]
    have hqQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hone : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    calc
      2 * (q : ℝ) ≤ 2 * (Q : ℝ) :=
        mul_le_mul_of_nonneg_left hqQr (by norm_num)
      _ ≤ 2 * (Q : ℝ) * (1 + ‖s‖) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℝ) ≤ 2 * Q)
  have hlog : Real.log (2 * (q : ℝ)) ≤ Real.log A :=
    Real.log_le_log hqpos hqA
  have hlog0 : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hlogA0 : 0 ≤ Real.log A := hlog0.trans hlog
  have hraw := norm_LFunction_sub_lemma3TruncatedL_le
    hχ hq2 (show 1 ≤ N by omega) hs
  calc
    ‖DirichletCharacter.LFunction χ s - lemma3TruncatedL N s χ‖ ≤
        12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) *
          (N : ℝ) ^ (-s.re) := hraw
    _ ≤ 12 * ‖s‖ * Real.log (2 * q) *
        (Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2)) := by
      have hnonneg : 0 ≤ 12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) := by
        positivity
      calc
        12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) *
            (N : ℝ) ^ (-s.re) ≤
          12 * ‖s‖ * Real.sqrt q * Real.log (2 * q) *
            (N : ℝ) ^ ((-1 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hpow hnonneg
        _ = _ := by ring
    _ ≤ 12 * ‖s‖ * Real.log A *
        (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by
      have hroot0 : 0 ≤ Real.sqrt q *
          (N : ℝ) ^ ((-1 : ℝ) / 2) := by positivity
      calc
        12 * ‖s‖ * Real.log (2 * q) *
            (Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2)) ≤
          12 * ‖s‖ * Real.log A *
            (Real.sqrt q * (N : ℝ) ^ ((-1 : ℝ) / 2)) := by
              gcongr
        _ ≤ 12 * ‖s‖ * Real.log A *
            (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by
              gcongr
    _ = 12 * ‖s‖ * Real.log (2 * (Q : ℝ) * (1 + ‖s‖)) *
        (1 + ‖s‖) ^ ((-1 : ℝ) / 2) := by rfl

/-- Fourth power of the pointwise truncation error. -/
theorem norm_LFunction_sub_lemma3Cutoff_pow_four_le
    {q Q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hqQ : q ≤ Q)
    (hQ : 2 ≤ Q) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s -
        lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 ≤
      20736 * ‖s‖ ^ 2 *
        (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
  let t : ℝ := ‖s‖
  let L : ℝ := Real.log (2 * (Q : ℝ) * (1 + ‖s‖))
  let z : ℝ := (1 + t) ^ ((-1 : ℝ) / 2)
  have ht0 : 0 ≤ t := norm_nonneg s
  have htp : 0 < 1 + t := by positivity
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    apply Real.log_nonneg
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [norm_nonneg s]
  have hzsq : z ^ 2 = (1 + t)⁻¹ := by
    dsimp only [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htp.le]
    norm_num
    rw [Real.rpow_neg_one]
  have htz : t * z ^ 2 ≤ 1 := by
    rw [hzsq, ← div_eq_mul_inv]
    exact (div_le_one htp).2 (by linarith)
  have htz0 : 0 ≤ t * z ^ 2 := mul_nonneg ht0 (sq_nonneg z)
  have htzsq : (t * z ^ 2) ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ htz0 zero_le_one).2 htz
  have hheight : t ^ 4 * z ^ 4 ≤ t ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left htzsq (sq_nonneg t)
    calc
      t ^ 4 * z ^ 4 = t ^ 2 * (t * z ^ 2) ^ 2 := by ring
      _ ≤ t ^ 2 * 1 := hmul
      _ = t ^ 2 := by ring
  have hpoint := norm_LFunction_sub_lemma3Cutoff_le
    hχ hq2 hqQ hQ hs
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hpoint 4
  calc
    ‖DirichletCharacter.LFunction χ s -
        lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 ≤
      (12 * t * L * z) ^ 4 := by simpa only [t, L, z] using hpow
    _ = 20736 * L ^ 4 * (t ^ 4 * z ^ 4) := by ring
    _ ≤ 20736 * L ^ 4 * t ^ 2 := by gcongr
    _ = 20736 * ‖s‖ ^ 2 *
        (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
      dsimp only [t, L]
      ring

/-- Summed fourth moment of the truncation error. -/
noncomputable def lemma3ErrorFourthTerm (Q q : ℕ) (s : ℂ) : ℝ :=
  if h : q = 0 then 0
  else
    have : NeZero q := ⟨h⟩
    primSum q (fun χ => ‖DirichletCharacter.LFunction χ s -
      lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4)

theorem lemma3_cutoff_error_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q →
      (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q, lemma3ErrorFourthTerm Q q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
  refine ⟨20736, by norm_num, ?_⟩
  intro Q s hQ hs
  let K : ℝ := 20736 * ‖s‖ ^ 2 *
    (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hinner : ∀ q ∈ Finset.Icc 2 Q,
      lemma3ErrorFourthTerm Q q s ≤ (Q : ℝ) * K := by
    intro q hq
    have hq2 := (Finset.mem_Icc.mp hq).1
    have hqQ := (Finset.mem_Icc.mp hq).2
    letI : NeZero q := ⟨by omega⟩
    rw [lemma3ErrorFourthTerm, dif_neg (by omega), primSum, tsum_fintype]
    calc
      (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖DirichletCharacter.LFunction χ s -
            lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 else 0) ≤
        ∑ _χ : DirichletCharacter ℂ q, K := by
          apply Finset.sum_le_sum
          intro χ hχmem
          by_cases hp : χ.IsPrimitive
          · simp only [hp, if_true]
            exact norm_LFunction_sub_lemma3Cutoff_pow_four_le
              hp hq2 hqQ hQ hs
          · simp [hp, hK0]
      _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) * K := by simp
      _ = (q.totient : ℝ) * K := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      _ ≤ (Q : ℝ) * K := by
        apply mul_le_mul_of_nonneg_right _ hK0
        exact_mod_cast (Nat.totient_le q).trans hqQ
  calc
    ∑ q ∈ Finset.Icc 2 Q, lemma3ErrorFourthTerm Q q s ≤
      ∑ _q ∈ Finset.Icc 2 Q, (Q : ℝ) * K := by
        exact Finset.sum_le_sum fun q hq => hinner q hq
    _ = ((Finset.Icc 2 Q).card : ℝ) * ((Q : ℝ) * K) := by simp
    _ ≤ (Q : ℝ) * ((Q : ℝ) * K) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hK0)
      rw [Nat.card_Icc]
      exact_mod_cast (show Q + 1 - 2 ≤ Q by omega)
    _ = 20736 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
      dsimp only [K]
      ring

theorem add_pow_four_le_eight (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]

theorem norm_pow_four_le_eight_add_error (x y : ℂ) :
    ‖x‖ ^ 4 ≤ 8 * (‖y‖ ^ 4 + ‖x - y‖ ^ 4) := by
  have hnorm : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc
      ‖x‖ = ‖y + (x - y)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
  exact (pow_le_pow_left₀ (norm_nonneg x) hnorm 4).trans
    (add_pow_four_le_eight _ _ (norm_nonneg y) (norm_nonneg _))

/-- The finite-polynomial contribution in the exact height-logarithmic
shape supported by Chen's calculation. -/
theorem lemma3_cutoff_truncated_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q →
      (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q,
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 else 0) ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
  rcases lemma3_truncated_fourth_moment with ⟨C₀, hC₀, hpoly⟩
  refine ⟨640 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro Q s hQ hs
  let N := lemma3Cutoff Q s
  let A : ℝ := 2 * (Q : ℝ) * (1 + ‖s‖)
  have hN2 : 2 ≤ N := lemma3Cutoff_two_le hQ
  have hQ1 : 1 ≤ Q := by omega
  have hNle : (N : ℝ) ≤ A := by
    simpa only [N, A] using lemma3Cutoff_le_two_mul (s := s) hQ1
  have hnormhalf : (1 / 2 : ℝ) ≤ ‖s‖ :=
    hs.trans (Complex.re_le_norm s)
  have hnorm0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have hsquare :
      (Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ) ≤
        40 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
    have hNle' : (N : ℝ) ≤
        2 * (Q : ℝ) * (1 + ‖s‖) := hNle
    have honeadd : 1 + ‖s‖ ≤ 3 * ‖s‖ := by linarith
    have hNle6 : (N : ℝ) ≤ 6 * (Q : ℝ) * ‖s‖ := by
      calc
        (N : ℝ) ≤ 2 * (Q : ℝ) * (1 + ‖s‖) := hNle'
        _ ≤ 2 * (Q : ℝ) * (3 * ‖s‖) := by gcongr
        _ = 6 * (Q : ℝ) * ‖s‖ := by ring
    have hNsq : ((N * N : ℕ) : ℝ) ≤
        36 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
      have h := (sq_le_sq₀ hNpos.le (by positivity :
        0 ≤ 6 * (Q : ℝ) * ‖s‖)).2 hNle6
      norm_num [pow_two, Nat.cast_mul] at h ⊢
      nlinarith
    -- A deliberately loose constant keeps the subsequent expression simple.
    have hQsq : (Q : ℝ) ^ 2 ≤
        4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
      have ht : (1 : ℝ) ≤ 4 * ‖s‖ ^ 2 := by
        nlinarith [sq_nonneg (‖s‖ - 1 / 2)]
      calc
        (Q : ℝ) ^ 2 = (Q : ℝ) ^ 2 * 1 := by ring
        _ ≤ (Q : ℝ) ^ 2 * (4 * ‖s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ht (sq_nonneg _)
        _ = 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by ring
    -- `N ≤ 2Q(1+|s|) ≤ 6Q|s|`, hence the natural constant here is 40.
    nlinarith
  have hlog : Real.log ((N * N : ℕ) : ℝ) ≤ 2 * Real.log A := by
    have hNNpos : (0 : ℝ) < ((N * N : ℕ) : ℝ) := by positivity
    have hNNle : ((N * N : ℕ) : ℝ) ≤ A ^ 2 := by
      have h := (sq_le_sq₀ hNpos.le hApos.le).2 hNle
      simpa [pow_two, Nat.cast_mul] using h
    calc
      Real.log ((N * N : ℕ) : ℝ) ≤ Real.log (A ^ 2) :=
        Real.log_le_log hNNpos hNNle
      _ = 2 * Real.log A := by rw [Real.log_pow]; norm_num
  have hlogN0 : 0 ≤ Real.log ((N * N : ℕ) : ℝ) :=
    Real.log_nonneg (by
      have hNNone : 1 ≤ N * N := by nlinarith
      exact_mod_cast hNNone)
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg (by
    dsimp only [A]
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith [norm_nonneg s])
  have hlogpow :
      (Real.log ((N * N : ℕ) : ℝ)) ^ 4 ≤
        16 * (Real.log A) ^ 4 := by
    calc
      (Real.log ((N * N : ℕ) : ℝ)) ^ 4 ≤
          (2 * Real.log A) ^ 4 := pow_le_pow_left₀ hlogN0 hlog 4
      _ = 16 * (Real.log A) ^ 4 := by ring
  calc
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
      C₀ * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
        (Real.log ((N * N : ℕ) : ℝ)) ^ 4 :=
      hpoly Q N s hN2 hs
    _ ≤ C₀ * (40 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2) *
        (16 * (Real.log A) ^ 4) := by gcongr
    _ = 640 * C₀ * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
      dsimp only [A]
      ring

/-- The form of Lemma 3 actually established by Chen's printed argument.

The finite Dirichlet polynomial is controlled by the multiplicative large
sieve, while the conditionally convergent tail is controlled uniformly by
Pólya--Vinogradov and Abel summation.  The height inside the logarithm is
retained: removing it is not justified by the calculation in the paper. -/
theorem lFunction_fourth_moment_with_height_log :
    Lemma3FourthMomentWithHeightLog := by
  rcases lemma3_cutoff_truncated_fourth_moment with
    ⟨Cpoly, hCpoly, hpoly⟩
  rcases lemma3_cutoff_error_fourth_moment with
    ⟨Cerr, hCerr, herr⟩
  refine ⟨8 * (Cpoly + Cerr), by positivity, ?_⟩
  intro Q s hQ hs
  let M : ℝ := (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
    (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4
  have hsplit :
      ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        8 *
          ((∑ q ∈ Finset.Icc 2 Q,
              ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
                ‖lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 else 0) +
            ∑ q ∈ Finset.Icc 2 Q, lemma3ErrorFourthTerm Q q s) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨by omega⟩
    rw [lFourthTerm, dif_neg (by omega), primSum, tsum_fintype]
    rw [lemma3ErrorFourthTerm, dif_neg (by omega), primSum, tsum_fintype]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro χ hχ
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true]
      simpa only [mul_add] using
        norm_pow_four_le_eight_add_error
          (DirichletCharacter.LFunction χ s)
          (lemma3TruncatedL (lemma3Cutoff Q s) s χ)
    · simp [hp]
  have hp :
      (∑ q ∈ Finset.Icc 2 Q,
          ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 else 0) ≤
        Cpoly * M := by
    have h := hpoly Q s hQ hs
    dsimp only [M]
    convert h using 1; ring
  have he :
      (∑ q ∈ Finset.Icc 2 Q, lemma3ErrorFourthTerm Q q s) ≤
        Cerr * M := by
    have h := herr Q s hQ hs
    dsimp only [M]
    convert h using 1; ring
  calc
    ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        8 *
          ((∑ q ∈ Finset.Icc 2 Q,
              ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
                ‖lemma3TruncatedL (lemma3Cutoff Q s) s χ‖ ^ 4 else 0) +
            ∑ q ∈ Finset.Icc 2 Q, lemma3ErrorFourthTerm Q q s) := hsplit
    _ ≤ 8 * (Cpoly * M + Cerr * M) := by gcongr
    _ = 8 * (Cpoly + Cerr) * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4 := by
      dsimp only [M]
      ring

end Chen
