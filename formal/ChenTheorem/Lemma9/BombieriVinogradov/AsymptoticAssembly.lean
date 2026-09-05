import ChenTheorem.Lemma9.BombieriVinogradov.ConductorAssembly
import ChenTheorem.Lemma6.PairBlockEstimate

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Parameters for the final Bombieri--Vinogradov estimate

We use the integer dyadic logarithm itself as the basic polylogarithmic
scale.  This avoids floor/ceiling errors while remaining comparable with
the real logarithm.
-/

/-- Positive integer proxy for `log x`. -/
def bvLogScale (x : ℕ) : ℕ := Nat.log 2 x + 1

/-- Common Vaughan and small-conductor cutoff. -/
def bvPolylogCutoff (K x : ℕ) : ℕ := bvLogScale x ^ K

theorem bvLogScale_pos (x : ℕ) : 1 ≤ bvLogScale x := by
  unfold bvLogScale
  omega

theorem bvPolylogCutoff_pos (K x : ℕ) : 1 ≤ bvPolylogCutoff K x := by
  unfold bvPolylogCutoff
  exact one_le_pow₀ (bvLogScale_pos x)

/-- The real logarithm is bounded by the next integer binary logarithm. -/
theorem real_log_le_bvLogScale {x : ℕ} (hx : 1 ≤ x) :
    Real.log (x : ℝ) ≤ (bvLogScale x : ℝ) := by
  have hxpow : x < 2 ^ (Nat.log 2 x + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) x
  have hxpowR : (x : ℝ) ≤ ((2 ^ (Nat.log 2 x + 1) : ℕ) : ℝ) := by
    exact_mod_cast hxpow.le
  have hlogmono :
      Real.log (x : ℝ) ≤
        Real.log (((2 : ℕ) ^ (Nat.log 2 x + 1) : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < x by omega)) hxpowR
  have hlogpow :
      Real.log (((2 : ℕ) ^ (Nat.log 2 x + 1) : ℕ) : ℝ) =
        ((Nat.log 2 x + 1 : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogpow] at hlogmono
  unfold bvLogScale
  have hlogtwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hscale0 : 0 ≤ ((Nat.log 2 x + 1 : ℕ) : ℝ) := by positivity
  exact hlogmono.trans
    (mul_le_of_le_one_right hscale0 hlogtwo)

/-- Conversely the integer logarithmic scale costs only an absolute factor. -/
theorem bvLogScale_cast_le_three_mul_log
    {x : ℕ} (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ)) :
    (bvLogScale x : ℝ) ≤ 3 * Real.log (x : ℝ) := by
  simpa only [bvLogScale, Nat.cast_add, Nat.cast_one] using
    natLog_two_add_one_le_three_mul_log hx hlogx

theorem log_pow_le_bvPolylogCutoff_cast
    (K : ℕ) {x : ℕ} (hx : 1 ≤ x) :
    Real.log (x : ℝ) ^ K ≤ (bvPolylogCutoff K x : ℝ) := by
  rw [bvPolylogCutoff, Nat.cast_pow]
  exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hx))
    (real_log_le_bvLogScale hx) K

theorem bvPolylogCutoff_cast_le
    (K : ℕ) {x : ℕ} (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ)) :
    (bvPolylogCutoff K x : ℝ) ≤
      3 ^ K * Real.log (x : ℝ) ^ K := by
  rw [bvPolylogCutoff, Nat.cast_pow]
  calc
    (bvLogScale x : ℝ) ^ K ≤ (3 * Real.log (x : ℝ)) ^ K :=
      pow_le_pow_left₀ (by positivity)
        (bvLogScale_cast_le_three_mul_log hx hlogx) K
    _ = 3 ^ K * Real.log (x : ℝ) ^ K := by ring

/-- Two polylogarithmic Vaughan cutoffs are eventually below `x`. -/
theorem eventually_bvPolylogCutoff_sq_le (K : ℕ) :
    ∀ᶠ x : ℕ in atTop, bvPolylogCutoff K x ^ 2 ≤ x := by
  have habsorb := eventually_const_mul_log_pow_le_rpow
    (3 ^ (2 * K) : ℝ) (2 * K) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [habsorb, eventually_ge_atTop 3,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)] with x habsorb hx hlogx
  have hcut := bvPolylogCutoff_cast_le (2 * K) (show 1 ≤ x by omega) hlogx
  have hpow : bvPolylogCutoff K x ^ 2 = bvPolylogCutoff (2 * K) x := by
    unfold bvPolylogCutoff
    rw [← pow_mul]
    ring_nf
  rw [hpow]
  have hreal : (bvPolylogCutoff (2 * K) x : ℝ) ≤ (x : ℝ) :=
    hcut.trans (by simpa only [Real.rpow_one] using habsorb)
  exact_mod_cast hreal

/-- For every positive level-loss exponent, the common polylogarithmic
cutoff itself eventually lies below the admissible Bombieri--Vinogradov
level.  This is used when a requested `Q` is smaller than the cutoff: one
may enlarge the nonnegative modulus sum to the cutoff. -/
theorem eventually_bvPolylogCutoff_le_level_self
    (B : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (bvPolylogCutoff (2 * B) x : ℝ) ≤
        Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B := by
  have habsorb := eventually_const_mul_log_pow_le_rpow
    (3 ^ (2 * B) : ℝ) (3 * B) (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [habsorb, eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)] with x habsorb hx hlogx
  change 1 ≤ Real.log (x : ℝ) at hlogx
  have hx1 : 1 ≤ x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hcut := bvPolylogCutoff_cast_le (2 * B) hx1 hlogx
  have hmul :
      (bvPolylogCutoff (2 * B) x : ℝ) * Real.log (x : ℝ) ^ B ≤
        (x : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      _ ≤ (3 ^ (2 * B) * Real.log (x : ℝ) ^ (2 * B)) *
          Real.log (x : ℝ) ^ B := by gcongr
      _ = 3 ^ (2 * B) * Real.log (x : ℝ) ^ (3 * B) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := habsorb
  rw [Real.sqrt_eq_rpow]
  exact (le_div_iff₀ (pow_pos hlogpos B)).2 hmul

theorem bvPolylogCutoff_sq_two_le
    (B x : ℕ) (hB : 1 ≤ B) (hx : 2 ≤ x) :
    2 ≤ bvPolylogCutoff (2 * B) x ^ 2 := by
  have hbase : 2 ≤ bvLogScale x := by
    unfold bvLogScale
    have := Nat.log_pos (by norm_num : 1 < 2) hx
    omega
  have hexp : 1 ≤ 2 * B := by omega
  have hcut : 2 ≤ bvPolylogCutoff (2 * B) x := by
    unfold bvPolylogCutoff
    calc
      2 ≤ bvLogScale x := hbase
      _ = bvLogScale x ^ 1 := by simp
      _ ≤ bvLogScale x ^ (2 * B) :=
        pow_le_pow_right₀ (by omega) hexp
  nlinarith

/-- Pure logarithmic upper bound for the Type-II conductor scale after the
standard parameter choice `U=V=H=L(x)^K`. -/
noncomputable def bvTypeIIScaleMajorant (B K : ℕ) (x : ℕ) : ℝ :=
  16 / Real.log (x : ℝ) ^ (2 * B) +
    5 / Real.log (x : ℝ) ^ K

theorem typeIIConductorScaleEnvelope_polylog_le
    (B K x Q : ℕ) (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hQ : (Q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B) :
    typeIIConductorScaleEnvelope
        (bvPolylogCutoff K x) Q
        (bvPolylogCutoff K x) (bvPolylogCutoff K x) x ≤
      bvTypeIIScaleMajorant B K x := by
  let L : ℝ := Real.log (x : ℝ)
  let P : ℝ := (bvPolylogCutoff K x : ℝ)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hP : L ^ K ≤ P := by
    dsimp only [L, P]
    exact log_pow_le_bvPolylogCutoff_cast K hx
  have hPpos : 0 < P := by
    dsimp only [P]
    exact_mod_cast (show 0 < bvPolylogCutoff K x by
      exact Nat.zero_lt_of_lt (bvPolylogCutoff_pos K x))
  have hQsq : (Q : ℝ) ^ 2 ≤ (x : ℝ) / L ^ (2 * B) := by
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt (x : ℝ) / L ^ B) ^ 2 := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg Q)
          (by simpa only [L] using hQ) 2
      _ = (x : ℝ) / L ^ (2 * B) := by
        rw [div_pow, Real.sq_sqrt hxpos.le]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have hfirst :
      16 * (Q : ℝ) ^ 2 / (x : ℝ) ≤ 16 / L ^ (2 * B) := by
    calc
      16 * (Q : ℝ) ^ 2 / (x : ℝ) ≤
          16 * ((x : ℝ) / L ^ (2 * B)) / (x : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQsq (by norm_num)) hxpos.le
      _ = 16 / L ^ (2 * B) := by field_simp
  have hcut : 2 / P ≤ 2 / L ^ K := by
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos K) hP
  have hpowmono : L ^ K ≤ L ^ (2 * K) := by
    exact pow_le_pow_right₀ hlogx (by omega)
  have hPsq : L ^ K ≤ P ^ 2 := by
    calc
      L ^ K ≤ L ^ (2 * K) := hpowmono
      _ = (L ^ K) ^ 2 := by rw [← pow_mul]; congr 1; omega
      _ ≤ P ^ 2 := pow_le_pow_left₀ (pow_nonneg hLpos.le K) hP 2
  have hlast : 1 / P ^ 2 ≤ 1 / L ^ K := by
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos K) hPsq
  unfold typeIIConductorScaleEnvelope bvTypeIIScaleMajorant
  dsimp only [L, P] at hfirst hcut hlast ⊢
  calc
    16 * (Q : ℝ) ^ 2 / (x : ℝ) +
          2 / (bvPolylogCutoff K x : ℝ) +
          2 / (bvPolylogCutoff K x : ℝ) +
          1 / (bvPolylogCutoff K x : ℝ) ^ 2 ≤
        16 / Real.log (x : ℝ) ^ (2 * B) +
          2 / Real.log (x : ℝ) ^ K +
          2 / Real.log (x : ℝ) ^ K +
          1 / Real.log (x : ℝ) ^ K := by
      exact add_le_add (add_le_add (add_le_add hfirst hcut) hcut) hlast
    _ = 16 / Real.log (x : ℝ) ^ (2 * B) +
          5 / Real.log (x : ℝ) ^ K := by ring

theorem typeIIConductorScaleEnvelope_polylog_two_mul_le
    (B x Q : ℕ) (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hQ : (Q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B) :
    typeIIConductorScaleEnvelope
        (bvPolylogCutoff (2 * B) x) Q
        (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x) x ≤
      21 / Real.log (x : ℝ) ^ (2 * B) := by
  calc
    typeIIConductorScaleEnvelope
        (bvPolylogCutoff (2 * B) x) Q
        (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x) x ≤
        bvTypeIIScaleMajorant B (2 * B) x :=
      typeIIConductorScaleEnvelope_polylog_le B (2 * B) x Q
        hx hlogx hQ
    _ = 21 / Real.log (x : ℝ) ^ (2 * B) := by
      unfold bvTypeIIScaleMajorant
      ring

/-- The explicit adjacent-endpoint Perron kernel mass costs only
`O(x log x)` at its natural height `T=x`. -/
theorem perronSharpKernelMass_at_nat_le
    (x : ℕ) (hx : 2 ≤ x) :
    4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
        2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (x : ℝ) ≤
      20 * (x : ℝ) * Real.log (2 * (x : ℝ)) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hupper : perronUpperPoint x ≤ 2 * (x : ℝ) := by
    unfold perronUpperPoint
    exact_mod_cast (show x + 1 ≤ 2 * x by omega)
  have hlog0 : 0 ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * x by omega))
  have hlog : Real.log (1 + (x : ℝ)) ≤ Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show 1 + x ≤ 2 * x by omega)
  have hlog1 : 0 ≤ Real.log (1 + (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 1 + x by omega))
  have hfirst :
      4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) ≤
        8 * (x : ℝ) * Real.log (2 * (x : ℝ)) := by
    calc
      4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) ≤
          4 * (2 * (x : ℝ)) * Real.log (2 * (x : ℝ)) := by
        gcongr
      _ = 8 * (x : ℝ) * Real.log (2 * (x : ℝ)) := by ring
  have htail :
      2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
          (x : ℝ) ≤ 10 * (x : ℝ) := by
    have hsquare : perronUpperPoint x ^ 2 ≤ (2 * (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by unfold perronUpperPoint; positivity) hupper 2
    unfold perronLowerPoint
    calc
      2 * (perronUpperPoint x ^ 2 + (x : ℝ) ^ 2) / (x : ℝ) ≤
          2 * ((2 * (x : ℝ)) ^ 2 + (x : ℝ) ^ 2) / (x : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hsquare le_rfl) (by norm_num))
          hxpos.le
      _ = 10 * (x : ℝ) := by field_simp; ring
  have hlogone : 1 ≤ Real.log (2 * (x : ℝ)) := by
    have hfour : (4 : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast (show 4 ≤ 2 * x by omega)
    have hmono : Real.log 4 ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by norm_num) hfour
    have hlogfour : 1 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith [Real.log_two_gt_d9]
    exact hlogfour.le.trans hmono
  calc
    4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
          2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
            (x : ℝ) ≤
        8 * (x : ℝ) * Real.log (2 * (x : ℝ)) + 10 * (x : ℝ) :=
      add_le_add hfirst htail
    _ ≤ 20 * (x : ℝ) * Real.log (2 * (x : ℝ)) := by
      nlinarith

theorem typeIIInteriorPairs_card_cast_le_nine_log_sq
    (x U V : ℕ) (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ)) :
    ((typeIIInteriorPairs x U V).card : ℝ) ≤
      9 * Real.log (x : ℝ) ^ 2 := by
  have hcard :
      ((typeIIInteriorPairs x U V).card : ℝ) ≤ (bvLogScale x : ℝ) ^ 2 := by
    exact_mod_cast card_typeIIInteriorPairs_le x U V
  have hscale := bvLogScale_cast_le_three_mul_log hx hlogx
  calc
    ((typeIIInteriorPairs x U V).card : ℝ) ≤
        (bvLogScale x : ℝ) ^ 2 := hcard
    _ ≤ (3 * Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hscale 2
    _ = 9 * Real.log (x : ℝ) ^ 2 := by ring

theorem typeIIBoundaryPairs_card_cast_le_nine_log_sq
    (x U V : ℕ) (hx : 1 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ)) :
    ((typeIIBoundaryPairs x U V).card : ℝ) ≤
      9 * Real.log (x : ℝ) ^ 2 := by
  have hcard :
      ((typeIIBoundaryPairs x U V).card : ℝ) ≤ (bvLogScale x : ℝ) ^ 2 := by
    exact_mod_cast card_typeIIBoundaryPairs_le x U V
  have hscale := bvLogScale_cast_le_three_mul_log hx hlogx
  calc
    ((typeIIBoundaryPairs x U V).card : ℝ) ≤
        (bvLogScale x : ℝ) ^ 2 := hcard
    _ ≤ (3 * Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hscale 2
    _ = 9 * Real.log (x : ℝ) ^ 2 := by ring

theorem conductor_block_count_cast_le_three_mul_log
    (H Q x : ℕ) (hQx : Q ≤ x) (hx : 1 ≤ x)
    (hlogx : 1 ≤ Real.log (x : ℝ)) :
    ((conductorDyadicIndices H Q).card : ℝ) ≤
      3 * Real.log (x : ℝ) := by
  have hcard := card_conductorDyadicIndices_le H Q
  have hlogmono : Nat.log 2 Q ≤ Nat.log 2 x := by
    exact Nat.log_mono_right hQx
  have hcast :
      ((conductorDyadicIndices H Q).card : ℝ) ≤ (bvLogScale x : ℝ) := by
    exact_mod_cast hcard.trans (Nat.add_le_add_right hlogmono 1)
  exact hcast.trans (bvLogScale_cast_le_three_mul_log hx hlogx)

theorem harmonic_cast_le_two_mul_log
    (Q x : ℕ) (hQ : 1 ≤ Q) (hQx : Q ≤ x)
    (hlogx : 1 ≤ Real.log (x : ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  have hlogmono : Real.log (Q : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q by omega))
      (by exact_mod_cast hQx)
  calc
    (harmonic Q : ℝ) ≤ 1 + Real.log (Q : ℝ) := harmonic_le_one_add_log Q
    _ ≤ 1 + Real.log (x : ℝ) := by linarith
    _ ≤ 2 * Real.log (x : ℝ) := by linarith

theorem sqrt_two_mul_sqrt_le_two_mul_rpow_quarter
    (x : ℕ) :
    Real.sqrt (2 * Real.sqrt (x : ℝ)) ≤
      2 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsqrtsqrt :
      Real.sqrt (Real.sqrt (x : ℝ)) =
        (x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hx0]
    congr 1
    norm_num
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hsqrtsqrt]
  exact mul_le_mul_of_nonneg_right hsqrt2 (Real.rpow_nonneg hx0 _)

theorem sqrt_two_mul_nat_le_two_mul_rpow_quarter
    (x Q : ℕ) (hQ : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    Real.sqrt (2 * (Q : ℝ)) ≤
      2 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
  calc
    Real.sqrt (2 * (Q : ℝ)) ≤
        Real.sqrt (2 * Real.sqrt (x : ℝ)) := by
      exact Real.sqrt_le_sqrt (by gcongr)
    _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 4) :=
      sqrt_two_mul_sqrt_le_two_mul_rpow_quarter x

/-- The two Type-I summands inside `uniformPrimitiveVaughanMajorant`. -/
noncomputable def uniformPrimitiveTypeIMajorant
    (C₂ : ℝ) (x U V Q : ℕ) : ℝ :=
  6 * ((2 * Q : ℕ) : ℝ) * (min U x : ℝ) * Real.sqrt (2 * Q) *
      Real.log (2 * ((2 * Q : ℕ) : ℝ)) * Real.log x +
    ((2 * Q : ℕ) : ℝ) *
      ((V : ℝ) * Real.log x +
        3 * (C₂ * ((U * V : ℕ) : ℝ) *
              Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
          Real.sqrt (2 * Q) * Real.log (2 * ((2 * Q : ℕ) : ℝ)))

noncomputable def bvTypeIMajorant
    (C₂ : ℝ) (B : ℕ) (x : ℕ) : ℝ :=
  (200 * (C₂ + 1) * 3 ^ (4 * B)) *
    (x : ℝ) ^ ((3 : ℝ) / 4) *
      Real.log (x : ℝ) ^ (4 * B + 6)

theorem uniformPrimitiveTypeIMajorant_polylog_le
    (C₂ : ℝ) (B x Q : ℕ) (hC₂ : 0 ≤ C₂)
    (hx : 2 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hQpos : 1 ≤ Q)
    (hQ : (Q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B)
    (hcutSq : bvPolylogCutoff (2 * B) x ^ 2 ≤ x) :
    uniformPrimitiveTypeIMajorant C₂ x
        (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x) Q ≤
      bvTypeIMajorant C₂ B x := by
  let L : ℝ := Real.log (x : ℝ)
  let P : ℝ := (bvPolylogCutoff (2 * B) x : ℝ)
  let Z : ℝ := (x : ℝ) ^ ((3 : ℝ) / 4)
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hL1 : 1 ≤ L := by simpa only [L] using hlogx
  have hP1 : 1 ≤ P := by
    dsimp only [P]
    exact_mod_cast bvPolylogCutoff_pos (2 * B) x
  have hPsq : P ^ 2 ≤ (x : ℝ) := by
    dsimp only [P]
    exact_mod_cast hcutSq
  have hLB : 1 ≤ L ^ B := one_le_pow₀ hL1
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    calc
      (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
        simpa only [L] using hQ
      _ ≤ Real.sqrt (x : ℝ) := div_le_self (Real.sqrt_nonneg _) hLB
  have hQx : Q ≤ x := by
    have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
      nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg (x : ℝ)]
    exact_mod_cast hQsqrt.trans hsqrtx
  have htwoQ : ((2 * Q : ℕ) : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
    push_cast
    gcongr
  have hsqrtQ := sqrt_two_mul_nat_le_two_mul_rpow_quarter x Q hQsqrt
  have hfourQ : 4 * Q ≤ x ^ 3 := by
    calc
      4 * Q ≤ 4 * x := Nat.mul_le_mul_left 4 hQx
      _ ≤ x ^ 2 * x := Nat.mul_le_mul_right x
        (by rw [pow_two, show (4 : ℕ) = 2 * 2 by norm_num]
            exact Nat.mul_le_mul hx hx)
      _ = x ^ 3 := by ring
  have hlogQ :
      Real.log (2 * ((2 * Q : ℕ) : ℝ)) ≤ 3 * L := by
    have harg : 2 * ((2 * Q : ℕ) : ℝ) ≤ (x : ℝ) ^ 3 := by
      have hfourQR : (4 * Q : ℝ) ≤ (x : ℝ) ^ 3 := by
        exact_mod_cast hfourQ
      push_cast
      nlinarith
    calc
      Real.log (2 * ((2 * Q : ℕ) : ℝ)) ≤ Real.log ((x : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) harg
      _ = 3 * L := by dsimp only [L]; rw [Real.log_pow]; norm_num
  have hlogQ0 : 0 ≤ Real.log (2 * ((2 * Q : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (2 * Q) by omega))
  have hPupper : P ≤ 3 ^ (2 * B) * L ^ (2 * B) := by
    dsimp only [P, L]
    exact bvPolylogCutoff_cast_le (2 * B) (show 1 ≤ x by omega) hlogx
  have hPsqupper : P ^ 2 ≤ 3 ^ (4 * B) * L ^ (4 * B) := by
    calc
      P ^ 2 ≤ (3 ^ (2 * B) * L ^ (2 * B)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hPupper 2
      _ = 3 ^ (4 * B) * L ^ (4 * B) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> ring
  have hlogP0 : 0 ≤ Real.log (P ^ 2) := Real.log_nonneg (by nlinarith)
  have hlogP : Real.log (P ^ 2) ≤ L := by
    exact Real.log_le_log (by positivity) hPsq
  have hcoeff :
      C₂ * P ^ 2 * Real.log (P ^ 2) ^ 5 + P ^ 2 ≤
        (C₂ + 1) * P ^ 2 * L ^ 5 := by
    have hLpow : 1 ≤ L ^ 5 := one_le_pow₀ hL1
    have hlogpow : Real.log (P ^ 2) ^ 5 ≤ L ^ 5 :=
      pow_le_pow_left₀ hlogP0 hlogP 5
    have hPterm : P ^ 2 ≤ P ^ 2 * L ^ 5 :=
      by exact le_mul_of_one_le_right (sq_nonneg P) hLpow
    calc
      C₂ * P ^ 2 * Real.log (P ^ 2) ^ 5 + P ^ 2 ≤
          C₂ * P ^ 2 * L ^ 5 + P ^ 2 * L ^ 5 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlogpow
            (mul_nonneg hC₂ (sq_nonneg P))) hPterm
      _ = (C₂ + 1) * P ^ 2 * L ^ 5 := by ring
  have hrootprod :
      Real.sqrt (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4) = Z := by
    dsimp only [Z]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
  have hsqrt_le_Z : Real.sqrt (x : ℝ) ≤ Z := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [Z]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hP_le_sq : P ≤ P ^ 2 := by nlinarith
  have hL_two_six : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by omega)
  have hL_one_six : L ≤ L ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 6 by omega)
  have htypeOne :
      6 * ((2 * Q : ℕ) : ℝ) * P * Real.sqrt (2 * Q) *
          Real.log (2 * ((2 * Q : ℕ) : ℝ)) * L ≤
        72 * P ^ 2 * Z * L ^ 6 := by
    calc
      6 * ((2 * Q : ℕ) : ℝ) * P * Real.sqrt (2 * Q) *
          Real.log (2 * ((2 * Q : ℕ) : ℝ)) * L ≤
          6 * (2 * Real.sqrt (x : ℝ)) * P *
            (2 * (x : ℝ) ^ ((1 : ℝ) / 4)) * (3 * L) * L := by
        gcongr
      _ = 72 * P * (Real.sqrt (x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 4)) * L ^ 2 := by ring
      _ = 72 * P * Z * L ^ 2 := by rw [hrootprod]
      _ ≤ 72 * P ^ 2 * Z * L ^ 6 := by gcongr
  have htypeTwoDirect :
      ((2 * Q : ℕ) : ℝ) * (P * L) ≤ 2 * P ^ 2 * Z * L ^ 6 := by
    calc
      ((2 * Q : ℕ) : ℝ) * (P * L) ≤
          (2 * Real.sqrt (x : ℝ)) * (P * L) := by gcongr
      _ ≤ 2 * Z * (P ^ 2 * L ^ 6) := by gcongr
      _ = 2 * P ^ 2 * Z * L ^ 6 := by ring
  have htypeTwoLong :
      ((2 * Q : ℕ) : ℝ) *
          (3 * (C₂ * P ^ 2 * Real.log (P ^ 2) ^ 5 + P ^ 2) *
            Real.sqrt (2 * Q) * Real.log (2 * ((2 * Q : ℕ) : ℝ))) ≤
        36 * (C₂ + 1) * P ^ 2 * Z * L ^ 6 := by
    calc
      ((2 * Q : ℕ) : ℝ) *
          (3 * (C₂ * P ^ 2 * Real.log (P ^ 2) ^ 5 + P ^ 2) *
            Real.sqrt (2 * Q) * Real.log (2 * ((2 * Q : ℕ) : ℝ))) ≤
          (2 * Real.sqrt (x : ℝ)) *
            (3 * ((C₂ + 1) * P ^ 2 * L ^ 5) *
              (2 * (x : ℝ) ^ ((1 : ℝ) / 4)) * (3 * L)) := by
        gcongr
      _ = 36 * (C₂ + 1) * P ^ 2 *
            (Real.sqrt (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4)) * L ^ 6 := by
        ring
      _ = 36 * (C₂ + 1) * P ^ 2 * Z * L ^ 6 := by rw [hrootprod]
  have hcutle : bvPolylogCutoff (2 * B) x ≤ x := by
    exact Nat.le_trans
      (show bvPolylogCutoff (2 * B) x ≤ bvPolylogCutoff (2 * B) x ^ 2 by
        have := bvPolylogCutoff_pos (2 * B) x
        nlinarith) hcutSq
  unfold uniformPrimitiveTypeIMajorant bvTypeIMajorant
  dsimp only [L, P, Z] at htypeOne htypeTwoDirect htypeTwoLong hPsqupper ⊢
  rw [min_eq_left (by exact_mod_cast hcutle :
    (bvPolylogCutoff (2 * B) x : ℝ) ≤ (x : ℝ))]
  push_cast
  have htypeOne' :
      6 * (2 * (Q : ℝ)) * (bvPolylogCutoff (2 * B) x : ℝ) *
          Real.sqrt (2 * (Q : ℝ)) * Real.log (2 * (2 * (Q : ℝ))) *
          Real.log (x : ℝ) ≤
        72 * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
          (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htypeOne
  have htypeTwoDirect' :
      (2 * (Q : ℝ)) *
          ((bvPolylogCutoff (2 * B) x : ℝ) * Real.log (x : ℝ)) ≤
        2 * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
          (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htypeTwoDirect
  have htypeTwoLong' :
      (2 * (Q : ℝ)) *
          (3 * (C₂ * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
                Real.log ((bvPolylogCutoff (2 * B) x : ℝ) ^ 2) ^ 5 +
                (bvPolylogCutoff (2 * B) x : ℝ) ^ 2) *
            Real.sqrt (2 * (Q : ℝ)) * Real.log (2 * (2 * (Q : ℝ)))) ≤
        36 * (C₂ + 1) * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
          (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htypeTwoLong
  have hsum :
      6 * (2 * (Q : ℝ)) * (bvPolylogCutoff (2 * B) x : ℝ) *
            Real.sqrt (2 * (Q : ℝ)) *
            Real.log (2 * (2 * (Q : ℝ))) * Real.log (x : ℝ) +
          (2 * (Q : ℝ)) *
            ((bvPolylogCutoff (2 * B) x : ℝ) * Real.log (x : ℝ) +
              3 * (C₂ * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
                    Real.log ((bvPolylogCutoff (2 * B) x : ℝ) ^ 2) ^ 5 +
                    (bvPolylogCutoff (2 * B) x : ℝ) ^ 2) *
                Real.sqrt (2 * (Q : ℝ)) * Real.log (2 * (2 * (Q : ℝ)))) ≤
        (72 + 2 + 36 * (C₂ + 1)) *
          (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
          (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
    calc
      _ =
          (6 * (2 * (Q : ℝ)) * (bvPolylogCutoff (2 * B) x : ℝ) *
              Real.sqrt (2 * (Q : ℝ)) * Real.log (2 * (2 * (Q : ℝ))) *
              Real.log (x : ℝ)) +
            ((2 * (Q : ℝ)) *
              ((bvPolylogCutoff (2 * B) x : ℝ) * Real.log (x : ℝ))) +
            ((2 * (Q : ℝ)) *
              (3 * (C₂ * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
                    Real.log ((bvPolylogCutoff (2 * B) x : ℝ) ^ 2) ^ 5 +
                    (bvPolylogCutoff (2 * B) x : ℝ) ^ 2) *
                Real.sqrt (2 * (Q : ℝ)) * Real.log (2 * (2 * (Q : ℝ))))) := by
            ring
      _ ≤ 72 * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
              (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 +
            2 * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
              (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 +
            36 * (C₂ + 1) * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
              (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
        exact add_le_add (add_le_add htypeOne' htypeTwoDirect') htypeTwoLong'
      _ = _ := by ring
  calc
    _ =
        6 * (2 * (Q : ℝ)) * (bvPolylogCutoff (2 * B) x : ℝ) *
              Real.sqrt (2 * (Q : ℝ)) *
              Real.log (2 * (2 * (Q : ℝ))) * Real.log (x : ℝ) +
            (2 * (Q : ℝ)) *
              ((bvPolylogCutoff (2 * B) x : ℝ) * Real.log (x : ℝ) +
                3 * (C₂ * (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
                      Real.log ((bvPolylogCutoff (2 * B) x : ℝ) ^ 2) ^ 5 +
                      (bvPolylogCutoff (2 * B) x : ℝ) ^ 2) *
                  Real.sqrt (2 * (Q : ℝ)) *
                  Real.log (2 * (2 * (Q : ℝ)))) := by
          simp only [pow_two]
    _ ≤ (72 + 2 + 36 * (C₂ + 1)) *
          (bvPolylogCutoff (2 * B) x : ℝ) ^ 2 *
          (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := hsum
    _ ≤ (200 * (C₂ + 1) * 3 ^ (4 * B)) *
          (x : ℝ) ^ ((3 : ℝ) / 4) *
          Real.log (x : ℝ) ^ (4 * B + 6) := by
      have hconst : 72 + 2 + 36 * (C₂ + 1) ≤ 200 * (C₂ + 1) := by
        nlinarith
      calc
        _ ≤ (200 * (C₂ + 1)) *
              (3 ^ (4 * B) * Real.log (x : ℝ) ^ (4 * B)) *
              (x : ℝ) ^ ((3 : ℝ) / 4) * Real.log (x : ℝ) ^ 6 := by
          gcongr
        _ = _ := by rw [pow_add]; ring

/-- On the range `x ≥ 2`, replacing `log (2x)` by `2 log x` costs no
more than an absolute factor. -/
theorem log_two_mul_nat_le_two_mul_log
    (x : ℕ) (hx : 2 ≤ x) :
    Real.log (2 * (x : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have harg : 2 * (x : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
  calc
    Real.log (2 * (x : ℝ)) ≤ Real.log ((x : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) harg
    _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num

/-- Algebraic square-root normalization used by both Type-II terms. -/
theorem typeII_sqrt_scale_le
    (A X L : ℝ) (B : ℕ) (hA : 0 ≤ A) (hX : 0 ≤ X) (hL : 1 ≤ L) :
    Real.sqrt
        (A * X ^ 2 * (21 / L ^ (2 * B)) * (2 * L) ^ 5) ≤
      Real.sqrt (672 * A) * X * L ^ 3 / L ^ B := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : L ^ (2 * B) = (L ^ B) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hL56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL (by omega)
    calc
      A * X ^ 2 * (21 / L ^ (2 * B)) * (2 * L) ^ 5 =
          672 * A * X ^ 2 * L ^ 5 / L ^ (2 * B) := by ring
      _ ≤ 672 * A * X ^ 2 * L ^ 6 / L ^ (2 * B) := by
        gcongr
      _ = (Real.sqrt (672 * A) * X * L ^ 3 / L ^ B) ^ 2 := by
        rw [hpow, div_pow]
        congr 1
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring

/-- The two Type-II summands inside `uniformPrimitiveVaughanMajorant`. -/
noncomputable def uniformPrimitiveTypeIIMajorant
    (Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ) (x U V H Q : ℕ) : ℝ :=
  ((typeIIInteriorPairs x U V).card : ℝ) *
      Real.sqrt
        (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
          typeIIConductorScaleEnvelope H Q U V x *
          Real.log (2 * (x : ℝ)) ^ 5) +
    ((typeIIBoundaryPairs x U V).card : ℝ) *
      ((1 / (2 * Real.pi)) *
        Real.sqrt
          (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
            typeIIConductorScaleEnvelope H Q U V x *
            Real.log (2 * (x : ℝ)) ^ 5) *
        (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
          2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
            (x : ℝ)))

theorem uniformPrimitiveVaughanMajorant_eq_typeI_add_typeII
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ) (x U V H Q : ℕ) :
    uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
        x U V H Q =
      uniformPrimitiveTypeIMajorant C₂ x U V Q +
        uniformPrimitiveTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁
          x U V H Q := by
  unfold uniformPrimitiveVaughanMajorant uniformPrimitiveTypeIMajorant
    uniformPrimitiveTypeIIMajorant
  ring

/-- Explicit logarithmically saving Type-II majorant.  The numerical
constants deliberately absorb the dyadic pair count and Perron mass. -/
noncomputable def bvTypeIIMajorant
    (Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ) (B : ℕ) (x : ℕ) : ℝ :=
  (9 * Real.sqrt (672 * (2 * Cᵢ₀ ^ 2 * Cᵢ₁)) +
      360 * Real.sqrt (672 * (2 * Cᵦ₀ ^ 2 * Cᵦ₁))) *
    (x : ℝ) * Real.log (x : ℝ) ^ 6 /
      Real.log (x : ℝ) ^ B

theorem uniformPrimitiveTypeIIMajorant_polylog_le
    (Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ) (B x Q : ℕ)
    (hCᵢ₁ : 0 ≤ Cᵢ₁) (hCᵦ₁ : 0 ≤ Cᵦ₁)
    (hx : 2 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hQ : (Q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B) :
    uniformPrimitiveTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x
        (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x)
        (bvPolylogCutoff (2 * B) x) Q ≤
      bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x := by
  let L : ℝ := Real.log (x : ℝ)
  let S : ℝ := typeIIConductorScaleEnvelope
    (bvPolylogCutoff (2 * B) x) Q
    (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x) x
  let M : ℝ :=
    4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
      2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) / (x : ℝ)
  let Aᵢ : ℝ := 2 * Cᵢ₀ ^ 2 * Cᵢ₁
  let Aᵦ : ℝ := 2 * Cᵦ₀ ^ 2 * Cᵦ₁
  have hx1 : 1 ≤ x := by omega
  have hxR0 : (0 : ℝ) ≤ x := by positivity
  have hL1 : 1 ≤ L := by simpa only [L] using hlogx
  have hL0 : 0 ≤ L := hL1.trans' zero_le_one
  have hLBpos : 0 < L ^ B := pow_pos (lt_of_lt_of_le zero_lt_one hL1) B
  have hAᵢ : 0 ≤ Aᵢ := by dsimp only [Aᵢ]; positivity
  have hAᵦ : 0 ≤ Aᵦ := by dsimp only [Aᵦ]; positivity
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    unfold typeIIConductorScaleEnvelope
    positivity
  have hS : S ≤ 21 / L ^ (2 * B) := by
    dsimp only [S, L]
    exact typeIIConductorScaleEnvelope_polylog_two_mul_le B x Q hx1 hlogx hQ
  have hlog2x0 : 0 ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * x by omega))
  have hlog2x : Real.log (2 * (x : ℝ)) ≤ 2 * L := by
    dsimp only [L]
    exact log_two_mul_nat_le_two_mul_log x hx
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    have hlog1 : 0 ≤ Real.log (1 + (x : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 1 + x by omega))
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (by unfold perronUpperPoint; positivity)) hlog1
    · exact div_nonneg (by positivity) (by positivity)
  have hM : M ≤ 40 * (x : ℝ) * L := by
    calc
      M ≤ 20 * (x : ℝ) * Real.log (2 * (x : ℝ)) := by
        dsimp only [M]
        exact perronSharpKernelMass_at_nat_le x hx
      _ ≤ 20 * (x : ℝ) * (2 * L) := by gcongr
      _ = 40 * (x : ℝ) * L := by ring
  have hrootᵢ :
      Real.sqrt (Aᵢ * (x : ℝ) ^ 2 * S *
          Real.log (2 * (x : ℝ)) ^ 5) ≤
        Real.sqrt (672 * Aᵢ) * (x : ℝ) * L ^ 3 / L ^ B := by
    calc
      _ ≤ Real.sqrt
          (Aᵢ * (x : ℝ) ^ 2 * (21 / L ^ (2 * B)) * (2 * L) ^ 5) := by
        apply Real.sqrt_le_sqrt
        gcongr
      _ ≤ _ := typeII_sqrt_scale_le Aᵢ (x : ℝ) L B hAᵢ hxR0 hL1
  have hrootᵦ :
      Real.sqrt (Aᵦ * S * Real.log (2 * (x : ℝ)) ^ 5) ≤
        Real.sqrt (672 * Aᵦ) * L ^ 3 / L ^ B := by
    calc
      _ ≤ Real.sqrt
          (Aᵦ * 1 ^ 2 * (21 / L ^ (2 * B)) * (2 * L) ^ 5) := by
        apply Real.sqrt_le_sqrt
        simp only [one_pow, mul_one]
        gcongr
      _ ≤ Real.sqrt (672 * Aᵦ) * 1 * L ^ 3 / L ^ B :=
        typeII_sqrt_scale_le Aᵦ 1 L B hAᵦ (by norm_num) hL1
      _ = _ := by ring
  have hcardᵢ :
      ((typeIIInteriorPairs x (bvPolylogCutoff (2 * B) x)
          (bvPolylogCutoff (2 * B) x)).card : ℝ) ≤ 9 * L ^ 2 := by
    dsimp only [L]
    exact typeIIInteriorPairs_card_cast_le_nine_log_sq x _ _ hx1 hlogx
  have hcardᵦ :
      ((typeIIBoundaryPairs x (bvPolylogCutoff (2 * B) x)
          (bvPolylogCutoff (2 * B) x)).card : ℝ) ≤ 9 * L ^ 2 := by
    dsimp only [L]
    exact typeIIBoundaryPairs_card_cast_le_nine_log_sq x _ _ hx1 hlogx
  have hpiCoeff0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hpiCoeff : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hL56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by omega)
  have hinterior :
      ((typeIIInteriorPairs x (bvPolylogCutoff (2 * B) x)
          (bvPolylogCutoff (2 * B) x)).card : ℝ) *
          Real.sqrt (Aᵢ * (x : ℝ) ^ 2 * S *
            Real.log (2 * (x : ℝ)) ^ 5) ≤
        9 * Real.sqrt (672 * Aᵢ) * (x : ℝ) * L ^ 6 / L ^ B := by
    calc
      _ ≤ (9 * L ^ 2) *
          (Real.sqrt (672 * Aᵢ) * (x : ℝ) * L ^ 3 / L ^ B) := by
        exact mul_le_mul hcardᵢ hrootᵢ (Real.sqrt_nonneg _) (by positivity)
      _ = 9 * Real.sqrt (672 * Aᵢ) * (x : ℝ) * L ^ 5 / L ^ B := by ring
      _ ≤ 9 * Real.sqrt (672 * Aᵢ) * (x : ℝ) * L ^ 6 / L ^ B := by
        gcongr
  have hboundary :
      ((typeIIBoundaryPairs x (bvPolylogCutoff (2 * B) x)
          (bvPolylogCutoff (2 * B) x)).card : ℝ) *
          ((1 / (2 * Real.pi)) *
            Real.sqrt (Aᵦ * S * Real.log (2 * (x : ℝ)) ^ 5) * M) ≤
        360 * Real.sqrt (672 * Aᵦ) * (x : ℝ) * L ^ 6 / L ^ B := by
    calc
      _ ≤ (9 * L ^ 2) *
          (1 * (Real.sqrt (672 * Aᵦ) * L ^ 3 / L ^ B) *
            (40 * (x : ℝ) * L)) := by
        gcongr
      _ = _ := by ring
  unfold uniformPrimitiveTypeIIMajorant bvTypeIIMajorant
  dsimp only [Aᵢ, Aᵦ, S, M, L] at hinterior hboundary ⊢
  exact (add_le_add hinterior hboundary).trans_eq (by ring)

/-- The complete uniform Vaughan majorant at the common polylogarithmic
cutoff, with its power-saving Type-I and logarithmically saving Type-II
parts displayed separately. -/
theorem uniformPrimitiveVaughanMajorant_polylog_le
    (C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ) (B x Q : ℕ)
    (hC₂ : 0 ≤ C₂) (hCᵢ₁ : 0 ≤ Cᵢ₁) (hCᵦ₁ : 0 ≤ Cᵦ₁)
    (hx : 2 ≤ x) (hlogx : 1 ≤ Real.log (x : ℝ))
    (hQpos : 1 ≤ Q)
    (hQ : (Q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B)
    (hcutSq : bvPolylogCutoff (2 * B) x ^ 2 ≤ x) :
    uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x
        (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x)
        (bvPolylogCutoff (2 * B) x) Q ≤
      bvTypeIMajorant C₂ B x +
        bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x := by
  rw [uniformPrimitiveVaughanMajorant_eq_typeI_add_typeII]
  exact add_le_add
    (uniformPrimitiveTypeIMajorant_polylog_le C₂ B x Q hC₂ hx hlogx
      hQpos hQ hcutSq)
    (uniformPrimitiveTypeIIMajorant_polylog_le Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x Q
      hCᵢ₁ hCᵦ₁ hx hlogx hQ)

/-- The large-conductor primitive mean after all dyadic blocks have been
assembled.  This is the analytic large-sieve half of Bombieri--Vinogradov;
the remaining `primitiveAdjustedMean x 0 H` is precisely the separate
small-conductor (Siegel--Walfisz) input. -/
theorem primitiveAdjustedMean_large_polylog_le :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (B x Q : ℕ),
        2 ≤ x → 1 ≤ Q → 1 ≤ Real.log (x : ℝ) →
          (Q : ℝ) ≤
            Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B →
          2 ≤ bvPolylogCutoff (2 * B) x ^ 2 →
          bvPolylogCutoff (2 * B) x ^ 2 ≤ x →
          primitiveAdjustedMean x (bvPolylogCutoff (2 * B) x) Q ≤
            3 * Real.log (x : ℝ) *
              (bvTypeIMajorant C₂ B x +
                bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x) := by
  rcases primitiveAdjustedMean_le_card_mul_uniformVaughanMajorant with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hmean⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro B x Q hx hQpos hlogx hQ hcutTwo hcutSq
  let P : ℕ := bvPolylogCutoff (2 * B) x
  have hx1 : 1 ≤ x := by omega
  have hP : 1 ≤ P := by
    dsimp only [P]
    exact bvPolylogCutoff_pos (2 * B) x
  have hLB : 1 ≤ Real.log (x : ℝ) ^ B := one_le_pow₀ hlogx
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    exact hQ.trans (div_le_self (Real.sqrt_nonneg _) hLB)
  have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hxR1 : (1 : ℝ) ≤ x := by exact_mod_cast hx1
      nlinarith
  have hQx : Q ≤ x := by exact_mod_cast hQsqrt.trans hsqrtx
  have hcount :
      ((conductorDyadicIndices P Q).card : ℝ) ≤
        3 * Real.log (x : ℝ) :=
    conductor_block_count_cast_le_three_mul_log P Q x hQx hx1 hlogx
  have hcutTwo' : 2 ≤ P * P := by
    simpa only [P, pow_two] using hcutTwo
  have hcutSq' : P * P ≤ x := by
    simpa only [P, pow_two] using hcutSq
  have hraw := hmean x P P P Q hx hP hP hP hcutTwo' hcutSq'
  have huniform := uniformPrimitiveVaughanMajorant_polylog_le
    C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x Q hC₂.le hCᵢ₁.le hCᵦ₁.le
      hx hlogx hQpos hQ hcutSq
  dsimp only [P] at hraw hcount ⊢
  calc
    primitiveAdjustedMean x (bvPolylogCutoff (2 * B) x) Q ≤
        ((conductorDyadicIndices (bvPolylogCutoff (2 * B) x) Q).card : ℝ) *
          uniformPrimitiveVaughanMajorant C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x
            (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x)
            (bvPolylogCutoff (2 * B) x) Q := hraw
    _ ≤ 3 * Real.log (x : ℝ) *
          (bvTypeIMajorant C₂ B x +
            bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x) := by
      exact mul_le_mul hcount huniform
        (uniformPrimitiveVaughanMajorant_nonneg
          C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ x
          (bvPolylogCutoff (2 * B) x) (bvPolylogCutoff (2 * B) x)
          (bvPolylogCutoff (2 * B) x) Q hC₂.le hCᵢ₁.le hCᵦ₁.le
          hx hP hP hP hQpos)
        (by positivity)

/-- Explicit reduction of the full progression mean at the standard
polylogarithmic cutoff.  All large-sieve, dyadic, induction and
imprimitive-character losses are now visible; only the small primitive
conductor mean remains as a separate summand. -/
theorem sum_maxProgressionError_polylog_reduction :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (B x Q : ℕ),
        2 ≤ x → 1 ≤ Q → 1 ≤ Real.log (x : ℝ) →
          (Q : ℝ) ≤
            Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B →
          bvPolylogCutoff (2 * B) x ≤ Q →
          2 ≤ bvPolylogCutoff (2 * B) x ^ 2 →
          bvPolylogCutoff (2 * B) x ^ 2 ≤ x →
          (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
            4 * Real.log (x : ℝ) ^ 2 *
                primitiveAdjustedMean x 0 (bvPolylogCutoff (2 * B) x) +
              12 * Real.log (x : ℝ) ^ 3 *
                (bvTypeIMajorant C₂ B x +
                  bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x) +
              12 * (x : ℝ) * Real.log (x : ℝ) ^ 2 /
                Real.log (x : ℝ) ^ (2 * B) := by
  rcases primitiveAdjustedMean_large_polylog_le with
    ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hlarge⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro B x Q hx hQpos hlogx hQ hcutQ hcutTwo hcutSq
  let L : ℝ := Real.log (x : ℝ)
  let P : ℕ := bvPolylogCutoff (2 * B) x
  let W : ℝ := bvTypeIMajorant C₂ B x +
    bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x
  have hx1 : 1 ≤ x := by omega
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (by simpa only [L] using hlogx)
  have hLB : 1 ≤ L ^ B := one_le_pow₀ (by simpa only [L] using hlogx)
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    exact hQ.trans (by simpa only [L] using div_le_self (Real.sqrt_nonneg _) hLB)
  have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hxR1 : (1 : ℝ) ≤ x := by exact_mod_cast hx1
      nlinarith
  have hQx : Q ≤ x := by exact_mod_cast hQsqrt.trans hsqrtx
  have hharm : (harmonic Q : ℝ) ≤ 2 * L := by
    dsimp only [L]
    exact harmonic_cast_le_two_mul_log Q x hQpos hQx hlogx
  have hlarge' : primitiveAdjustedMean x P Q ≤ 3 * L * W := by
    dsimp only [P, L, W]
    exact hlarge B x Q hx hQpos hlogx hQ hcutTwo hcutSq
  have hQsq : (Q : ℝ) ^ 2 ≤ (x : ℝ) / L ^ (2 * B) := by
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt (x : ℝ) / L ^ B) ^ 2 := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg Q) (by simpa only [L] using hQ) 2
      _ = (x : ℝ) / L ^ (2 * B) := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have hlogNat : ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤ 3 * L := by
    simpa only [bvLogScale, L] using
      bvLogScale_cast_le_three_mul_log hx1 hlogx
  have hlogNat' : (Nat.log 2 x : ℝ) + 1 ≤ 3 * L := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlogNat
  have hQplus : (Q + 1 : ℝ) ≤ 2 * (Q : ℝ) := by
    exact_mod_cast (show Q + 1 ≤ 2 * Q by omega)
  have herror :
      2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * L ≤
        12 * (x : ℝ) * L ^ 2 / L ^ (2 * B) := by
    calc
      _ ≤ 2 * (Q : ℝ) * (2 * (Q : ℝ)) * (3 * L) * L := by
        gcongr
      _ = 12 * (Q : ℝ) ^ 2 * L ^ 2 := by ring
      _ ≤ 12 * ((x : ℝ) / L ^ (2 * B)) * L ^ 2 := by gcongr
      _ = 12 * (x : ℝ) * L ^ 2 / L ^ (2 * B) := by ring
  have hW0 : 0 ≤ W := by
    dsimp only [W, bvTypeIMajorant, bvTypeIIMajorant]
    positivity
  have hsmall0 : 0 ≤ primitiveAdjustedMean x 0 P :=
    primitiveAdjustedMean_nonneg x 0 P
  have hharm0 : 0 ≤ (harmonic Q : ℝ) := by
    have hrat : (0 : ℚ) ≤ harmonic Q := by
      unfold harmonic
      exact Finset.sum_nonneg fun i _ => inv_nonneg.2 (by positivity)
    exact_mod_cast hrat
  have hbase := sum_maxProgressionError_le_small_add_large_add_error
    x P Q hx hcutQ
  dsimp only [L, P, W] at hbase hlarge' hharm herror hW0 hsmall0 ⊢
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
        (harmonic Q : ℝ) ^ 2 *
            (primitiveAdjustedMean x 0 (bvPolylogCutoff (2 * B) x) +
              primitiveAdjustedMean x (bvPolylogCutoff (2 * B) x) Q) +
          2 * (Q : ℝ) * (Q + 1 : ℝ) *
            (Nat.log 2 x + 1 : ℝ) * Real.log (x : ℝ) := hbase
    _ ≤ (2 * Real.log (x : ℝ)) ^ 2 *
            (primitiveAdjustedMean x 0 (bvPolylogCutoff (2 * B) x) +
              3 * Real.log (x : ℝ) *
                (bvTypeIMajorant C₂ B x +
                  bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x)) +
          12 * (x : ℝ) * Real.log (x : ℝ) ^ 2 /
            Real.log (x : ℝ) ^ (2 * B) := by
      exact add_le_add
        (mul_le_mul
          (pow_le_pow_left₀ hharm0 hharm 2)
          (add_le_add le_rfl hlarge')
          (add_nonneg hsmall0 (primitiveAdjustedMean_nonneg _ _ _))
          (sq_nonneg _))
        herror
    _ = _ := by ring

end Chen.BombieriVinogradov
