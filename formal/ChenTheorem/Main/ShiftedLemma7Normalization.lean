import ChenTheorem.Main.ShiftedLemma7

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! # Fixed-shift normalization for Lemma 7

For a fixed positive even shift `h`, compare the shifted normalizing sum at
scale `x` with the original normalizing sum at the largest dyadic multiple of
`h` below `x`.  This comparison preserves the odd prime factors—and hence the
singular series—while the comparison scale stays within a factor two of `x`.
-/

def shiftedLemma7ComparisonScale (h x : ℕ) : ℕ :=
  h * 2 ^ Nat.log 2 (x / h)

theorem shiftedLemma7ComparisonScale_le
    {h x : ℕ} (hh0 : 0 < h) (hhx : h ≤ x) :
    shiftedLemma7ComparisonScale h x ≤ x := by
  have hq0 : 0 < x / h := Nat.div_pos hhx hh0
  have hp := Nat.pow_log_le_self 2 hq0.ne'
  calc
    shiftedLemma7ComparisonScale h x =
        h * 2 ^ Nat.log 2 (x / h) := rfl
    _ ≤ h * (x / h) := Nat.mul_le_mul_left h hp
    _ = (x / h) * h := by rw [mul_comm]
    _ ≤ x := Nat.div_mul_le_self x h

theorem lt_two_mul_shiftedLemma7ComparisonScale
    {h x : ℕ} (hh0 : 0 < h) (hhx : h ≤ x) :
    x < 2 * shiftedLemma7ComparisonScale h x := by
  let q := x / h
  let p := 2 ^ Nat.log 2 q
  have hq0 : 0 < q := by dsimp only [q]; exact Nat.div_pos hhx hh0
  have hqpow : q < 2 ^ (Nat.log 2 q + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
  have hqle : q + 1 ≤ 2 * p := by
    dsimp only [p] at ⊢
    rw [pow_succ] at hqpow
    omega
  have hmod : x % h < h := Nat.mod_lt x hh0
  have hdecomp : x % h + h * (x / h) = x := Nat.mod_add_div x h
  calc
    x = x % h + h * q := by simpa only [q] using hdecomp.symm
    _ < h + h * q := by omega
    _ = h * (q + 1) := by ring
    _ ≤ h * (2 * p) := Nat.mul_le_mul_left h hqle
    _ = 2 * shiftedLemma7ComparisonScale h x := by
      dsimp only [shiftedLemma7ComparisonScale, p, q]
      ring

theorem tendsto_shiftedLemma7ComparisonScale_atTop
    {h : ℕ} (hh0 : 0 < h) :
    Tendsto (shiftedLemma7ComparisonScale h) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max h (2 * b), ?_⟩
  intro x hx
  have hhx : h ≤ x := (le_max_left h (2 * b)).trans hx
  have h2b : 2 * b ≤ x := (le_max_right h (2 * b)).trans hx
  have hlt := lt_two_mul_shiftedLemma7ComparisonScale hh0 hhx
  omega

theorem shiftedLemma7ComparisonScale_pos
    {h x : ℕ} (hh0 : 0 < h) :
    0 < shiftedLemma7ComparisonScale h x := by
  unfold shiftedLemma7ComparisonScale
  positivity

/-- Multiplying the fixed shift by a power of two does not change its odd
prime factors. -/
theorem primeFactors_shiftedLemma7ComparisonScale_filter
    {h x : ℕ} (hh0 : 0 < h) :
    (shiftedLemma7ComparisonScale h x).primeFactors.filter (2 < ·) =
      h.primeFactors.filter (2 < ·) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpY, hp2⟩
    rw [Nat.mem_primeFactors] at hpY
    rcases hpY with ⟨hpprime, hpdiv, hpY0⟩
    have hp2ne : p ≠ 2 := by omega
    have hpnotpow : ¬p ∣ 2 ^ Nat.log 2 (x / h) := by
      intro hp
      exact hp2ne
        ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp
          (hpprime.dvd_of_dvd_pow hp))
    have hph : p ∣ h := by
      rcases hpprime.dvd_mul.mp hpdiv with hph | hpPow
      · exact hph
      · exact (hpnotpow hpPow).elim
    exact ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hph, hh0.ne'⟩, hp2⟩
  · rintro ⟨hph, hp2⟩
    rw [Nat.mem_primeFactors] at hph
    rcases hph with ⟨hpprime, hpdiv, hhne⟩
    have hpY : p ∣ shiftedLemma7ComparisonScale h x := by
      unfold shiftedLemma7ComparisonScale
      exact dvd_mul_of_dvd_left hpdiv _
    exact ⟨Nat.mem_primeFactors.mpr
      ⟨hpprime, hpY, (shiftedLemma7ComparisonScale_pos hh0).ne'⟩, hp2⟩

theorem chenConst_shiftedLemma7ComparisonScale
    {h x : ℕ} (hh0 : 0 < h) :
    chenConst (shiftedLemma7ComparisonScale h x) = chenConst h := by
  unfold chenConst
  rw [primeFactors_shiftedLemma7ComparisonScale_filter hh0]

theorem even_shiftedLemma7ComparisonScale
    {h x : ℕ} (hhEven : Even h) :
    Even (shiftedLemma7ComparisonScale h x) := by
  rcases hhEven with ⟨a, ha⟩
  refine ⟨a * 2 ^ Nat.log 2 (x / h), ?_⟩
  unfold shiftedLemma7ComparisonScale
  rw [ha]
  ring

/-- The original normalizing set at the dyadic comparison scale embeds in
the shifted normalizing set at `x`. -/
theorem sieveNorm_comparisonScale_le_shiftedSieveNorm
    {h x : ℕ} {ε : ℝ} (hh0 : 0 < h) (hhEven : Even h)
    (hhx : h ≤ x) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    sieveNorm (shiftedLemma7ComparisonScale h x) ε ≤
      shiftedSieveNorm h x ε := by
  let y := shiftedLemma7ComparisonScale h x
  have hyx : y ≤ x := shiftedLemma7ComparisonScale_le hh0 hhx
  have hy0 : 0 < y := shiftedLemma7ComparisonScale_pos hh0
  have hα0 : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hsubset : sieveNormIndices y ε ⊆
      shiftedSieveNormIndices h x ε := by
    intro k hk
    have hk' := hk
    simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range] at hk'
    have hky : k ≤ y := by omega
    have hkx : k < x + 1 := hky.trans_lt (by omega)
    have hcut : (k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
      calc
        (k : ℝ) ≤ (y : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hk'.2.2.1
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
          exact Real.rpow_le_rpow (by positivity)
            (by exact_mod_cast hyx) hα0
    have hhy : h ∣ y := by
      dsimp only [y, shiftedLemma7ComparisonScale]
      exact dvd_mul_right h _
    have hcop : k.Coprime h :=
      Nat.Coprime.of_dvd_right hhy hk'.2.2.2
    simp only [shiftedSieveNormIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkx, hk'.2.1, hcut, hcop⟩
  rw [sieveNorm, shiftedSieveNorm]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro k hkShift hkOriginal
  have hk' := hkShift
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  have hk2 : k.Coprime 2 :=
    Nat.Coprime.of_dvd_right hhEven.two_dvd hk'.2.2.2
  have hkodd : Odd k := hk2.odd_of_right
  exact div_nonneg (sq_nonneg _) (fW_pos_of_odd (by omega) hkodd).le

/-- The fixed factor-two loss between `x` and the dyadic comparison scale is
absorbed by one unit of `ε` in the coefficient. -/
theorem eventually_log_div_shiftedCoefficient_le_shiftedSieveNorm
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) / ((8 + 21 * ε) * chenConst h) ≤
        shiftedSieveNorm h x ε := by
  let y : ℕ → ℕ := shiftedLemma7ComparisonScale h
  let T : ℝ := (8 + 20 * ε) * Real.log 2 / ε
  have hyT : Tendsto y atTop atTop :=
    tendsto_shiftedLemma7ComparisonScale_atTop hh0
  have hlogyT : Tendsto (fun x : ℕ => Real.log (y x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hyT)
  have horiginal := hyT.eventually
    (eventually_log_div_coefficient_le_sieveNorm ε hε hε')
  have hloglarge := hlogyT.eventually (eventually_ge_atTop T)
  filter_upwards [horiginal, hloglarge, eventually_ge_atTop h] with
    x horiginal hloglarge hhx
  have hx0 : 0 < x := hh0.trans_le hhx
  have hy0 : 0 < y x := by
    exact shiftedLemma7ComparisonScale_pos hh0
  have hlt : x < 2 * y x := by
    exact lt_two_mul_shiftedLemma7ComparisonScale hh0 hhx
  have hlogxy : Real.log (x : ℝ) ≤ Real.log 2 + Real.log (y x : ℝ) := by
    have hcast : (x : ℝ) ≤ 2 * (y x : ℝ) := by exact_mod_cast hlt.le
    calc
      Real.log (x : ℝ) ≤ Real.log (2 * (y x : ℝ)) :=
        Real.log_le_log (by positivity) hcast
      _ = Real.log 2 + Real.log (y x : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
  have hA : 0 < 8 + 20 * ε := by positivity
  have hB : 0 < 8 + 21 * ε := by positivity
  have hC : 0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  have habsorb : (8 + 20 * ε) * Real.log 2 ≤
      ε * Real.log (y x : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hloglarge hε.le
    dsimp only [T] at hmul
    field_simp at hmul
    linarith
  have hlogs : (8 + 20 * ε) * Real.log (x : ℝ) ≤
      (8 + 21 * ε) * Real.log (y x : ℝ) := by
    nlinarith
  have hratio :
      Real.log (x : ℝ) / ((8 + 21 * ε) * chenConst h) ≤
        Real.log (y x : ℝ) / ((8 + 20 * ε) * chenConst h) := by
    rw [div_le_div_iff₀ (mul_pos hB hC) (mul_pos hA hC)]
    nlinarith
  calc
    Real.log (x : ℝ) / ((8 + 21 * ε) * chenConst h) ≤
        Real.log (y x : ℝ) / ((8 + 20 * ε) * chenConst h) := hratio
    _ = Real.log (y x : ℝ) /
        ((8 + 20 * ε) * chenConst (y x)) := by
      rw [chenConst_shiftedLemma7ComparisonScale hh0]
    _ ≤ sieveNorm (y x) ε := horiginal (even_shiftedLemma7ComparisonScale hhEven)
    _ ≤ shiftedSieveNorm h x ε :=
      sieveNorm_comparisonScale_le_shiftedSieveNorm
        hh0 hhEven hhx hε.le (by linarith)

end Chen
