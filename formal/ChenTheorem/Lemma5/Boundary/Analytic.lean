import ChenTheorem.Lemma5.Boundary.Mass

/-!
# Analytic estimates for the boundary term in Chen's Lemma 5

The algebraic Selberg optimization is complete in
`Lemma5/Boundary/Weights.lean`.  This file chooses a small power level and
develops the remaining uniform estimates for its normalization and for
the outer prime-pair sum.
-/

open Filter Real
open scoped Classical Topology

namespace Chen

/-- The reciprocal weight of the admissible Chen pairs is bounded by
the square of the prime harmonic sum.  Retaining primality here avoids
the two full logarithms lost by the ordinary harmonic-series bound. -/
theorem sum_pairQuotient_le_primeReciprocalSq (x : ℕ) :
    ∑ q ∈ chenPairs x,
        (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
      (x : ℝ) *
        (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by
  let box : Finset (ℕ × ℕ) := x.primesLE ×ˢ x.primesLE
  have hsubset : chenPairs x ⊆ box := by
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    exact Finset.mem_product.mpr
      ⟨Nat.mem_primesLE.mpr ⟨by omega, hq'.2.1⟩,
        Nat.mem_primesLE.mpr ⟨by omega, hq'.2.2.1⟩⟩
  calc
    ∑ q ∈ chenPairs x,
        (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
        ∑ q ∈ box,
          (x : ℝ) / ((q.1 : ℝ) * q.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q _ _
      positivity
    _ = (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by
      simp only [box, Finset.sum_product, div_eq_mul_inv, mul_inv]
      calc
        (∑ a ∈ x.primesLE, ∑ b ∈ x.primesLE,
            (x : ℝ) * ((a : ℝ)⁻¹ * (b : ℝ)⁻¹)) =
            (x : ℝ) *
              ((∑ a ∈ x.primesLE, (a : ℝ)⁻¹) *
                ∑ b ∈ x.primesLE, (b : ℝ)⁻¹) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = (x : ℝ) *
            (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by ring

theorem exp_two_mul_sub_one_le_four_mul
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : 2 * t ≤ 1) :
    Real.exp (2 * t) - 1 ≤ 4 * t := by
  let u : ℝ := 2 * t
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu1 : ‖u‖ ≤ 1 := by
    rw [Real.norm_of_nonneg hu0]
    exact ht1
  have hrem := Real.norm_exp_sub_one_sub_id_le hu1
  have hremUpper :
      Real.exp u - 1 - u ≤ u ^ 2 := by
    calc
      Real.exp u - 1 - u ≤ ‖Real.exp u - 1 - u‖ :=
        le_norm_self _
      _ ≤ ‖u‖ ^ 2 := hrem
      _ = u ^ 2 := by rw [Real.norm_of_nonneg hu0]
  have husq : u ^ 2 ≤ u := by
    nlinarith
  dsimp only [u] at hremUpper husq ⊢
  nlinarith

/-- The transition interval has relative width
`O((log x)^(-1/10))`, with the harmless extra `1` coming from its
integer endpoints. -/
theorem smoothingTransition_width_le
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (hsmall :
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1) :
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ) ≤
      4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
          (Real.log x) ^ (-(0.1 : ℝ)) + 1 := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let t : ℝ := (Real.log x) ^ (-(0.1 : ℝ))
  let E : ℝ := Real.exp (2 * t)
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hEpos : 0 < E := by
    dsimp only [E]
    positivity
  have hEone : 1 ≤ E := by
    dsimp only [E]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  have hEsub :
      E - 1 ≤ 4 * t := by
    dsimp only [E]
    exact exp_two_mul_sub_one_le_four_mul ht0 (by
      dsimp only [t]
      exact hsmall)
  have hY0 : 0 ≤ Y := by
    dsimp only [Y]
    positivity
  have hLU :
      smoothingTransitionLower x q ≤
        smoothingTransitionUpper x q :=
    smoothingTransitionLower_le_upper hq
  have hU :
      (smoothingTransitionUpper x q : ℝ) ≤ Y := by
    unfold smoothingTransitionUpper
    dsimp only [Y]
    exact Nat.floor_le (by positivity)
  have hL :
      Y / E - 1 ≤
        (smoothingTransitionLower x q : ℝ) := by
    have hfloor :
        Y / E <
          (smoothingTransitionLower x q : ℝ) + 1 := by
      unfold smoothingTransitionLower
      dsimp only [Y, E, t]
      exact Nat.lt_floor_add_one
        (((x : ℝ) / ((q.1 : ℝ) * q.2)) /
          Real.exp
            (2 * (Real.log x) ^ (-(0.1 : ℝ))))
    linarith
  have hwidth :
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) ≤
        Y - Y / E + 1 := by
    rw [Nat.cast_sub hLU]
    linarith
  have hYdiv : Y / E ≤ Y := div_le_self hY0 hEone
  have hidentity :
      Y - Y / E = (Y / E) * (E - 1) := by
    field_simp
  have hrelative :
      Y - Y / E ≤ Y * (E - 1) := by
    rw [hidentity]
    exact mul_le_mul hYdiv le_rfl (sub_nonneg.mpr hEone) hY0
  calc
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ) ≤
        Y - Y / E + 1 := hwidth
    _ ≤ Y * (E - 1) + 1 := by linarith
    _ ≤ Y * (4 * t) + 1 := by gcongr
    _ = 4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
          (Real.log x) ^ (-(0.1 : ℝ)) + 1 := by
      dsimp only [Y, t]
      ring

theorem eventually_transition_width_small :
    ∀ᶠ x : ℕ in atTop,
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1 := by
  have hreal :
      Tendsto (fun y : ℝ =>
        2 * y ^ (-(0.1 : ℝ))) atTop (𝓝 0) := by
    have hrpow :
        Tendsto (fun y : ℝ => y ^ (-(0.1 : ℝ)))
          atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.1)
    have htwo :
        Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa only [mul_zero] using htwo.mul hrpow
  have hlogNat :
      Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (hreal.comp hlogNat).eventually
    (eventually_le_nhds zero_lt_one)

/-- The pair range supplies exactly the logarithm needed to cancel the
von Mangoldt bound in the boundary sum. -/
theorem pairLog_inv_mul_log_le_three
    {x : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) :
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        Real.log x ≤ 3 := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
    rpow_third_lt_pairQuotient hq
  have hpowpos :
      0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hlogLower :
      (1 : ℝ) / 3 * Real.log x ≤ Real.log Y := by
    calc
      (1 : ℝ) / 3 * Real.log x =
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) := by
        rw [Real.log_rpow hxpos]
      _ ≤ Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
  have hlogY : 0 < Real.log Y := by
    linarith
  change (Real.log Y)⁻¹ * Real.log x ≤ 3
  rw [inv_mul_eq_div, div_le_iff₀ hlogY]
  nlinarith

theorem sum_smoothingTransition_width_le
    {x : ℕ}
    (hsmall :
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1) :
    ∑ q ∈ chenPairs x,
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) ≤
      4 * (Real.log x) ^ (-(0.1 : ℝ)) * (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 +
        ((chenPairs x).card : ℝ) := by
  calc
    ∑ q ∈ chenPairs x,
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) ≤
        ∑ q ∈ chenPairs x,
          (4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
              (Real.log x) ^ (-(0.1 : ℝ)) + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      exact smoothingTransition_width_le hq hsmall
    _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
          (∑ q ∈ chenPairs x,
            (x : ℝ) / ((q.1 : ℝ) * q.2)) +
          ((chenPairs x).card : ℝ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      calc
        (∑ q ∈ chenPairs x,
            4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
              (Real.log x) ^ (-(0.1 : ℝ))) +
              ((chenPairs x).card : ℝ) * 1 =
            (∑ q ∈ chenPairs x,
              4 * (Real.log x) ^ (-(0.1 : ℝ)) *
                ((x : ℝ) / ((q.1 : ℝ) * q.2))) +
              ((chenPairs x).card : ℝ) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro q hq
            ring
          · ring
        _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
              (∑ q ∈ chenPairs x,
                (x : ℝ) / ((q.1 : ℝ) * q.2)) +
              ((chenPairs x).card : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
          ((x : ℝ) *
            (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2) +
          ((chenPairs x).card : ℝ) := by
      gcongr
      exact sum_pairQuotient_le_primeReciprocalSq x
    _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) * (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 +
        ((chenPairs x).card : ℝ) := by ring

/-- A deliberately small Selberg level.  The exponent leaves ample room
for the polynomial congruence-count error. -/
noncomputable def transitionSelbergLevel (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 10000)⌋₊

theorem one_le_transitionSelbergLevel {x : ℕ} (hx : 1 ≤ x) :
    1 ≤ transitionSelbergLevel x := by
  unfold transitionSelbergLevel
  rw [Nat.le_floor_iff (by positivity)]
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  simpa using Real.one_le_rpow hxR (by norm_num :
    (0 : ℝ) ≤ (1 : ℝ) / 10000)

theorem transitionSelbergLevel_le_cutoff {x : ℕ} (hx : 1 ≤ x) :
    transitionSelbergLevel x ≤ transitionSieveCutoff x := by
  unfold transitionSelbergLevel transitionSieveCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hx) (by norm_num)

theorem transitionSelbergLevel_cast_le_rpow (x : ℕ) :
    (transitionSelbergLevel x : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 10000) := by
  unfold transitionSelbergLevel
  exact Nat.floor_le (by positivity)

/-- Half the logarithmic Selberg level, used for the two squarefree
factors in the lower-bound convolution. -/
noncomputable def transitionSelbergHalfLevel (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 20000)⌋₊

theorem transitionSelbergHalfLevel_sq_le_level
    {x : ℕ} (hx : 1 ≤ x) :
    transitionSelbergHalfLevel x ^ 2 ≤ transitionSelbergLevel x := by
  unfold transitionSelbergLevel
  rw [Nat.le_floor_iff (by positivity)]
  have hY :
      (transitionSelbergHalfLevel x : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 20000) := by
    unfold transitionSelbergHalfLevel
    exact Nat.floor_le (by positivity)
  have hYnonneg : (0 : ℝ) ≤ transitionSelbergHalfLevel x := by positivity
  have hsq :
      (transitionSelbergHalfLevel x : ℝ) ^ 2 ≤
        ((x : ℝ) ^ ((1 : ℝ) / 20000)) ^ 2 :=
    pow_le_pow_left₀ hYnonneg hY 2
  norm_num only [Nat.cast_pow]
  calc
    (transitionSelbergHalfLevel x : ℝ) ^ 2 ≤
        ((x : ℝ) ^ ((1 : ℝ) / 20000)) ^ 2 := hsq
    _ = (x : ℝ) ^ ((1 : ℝ) / 10000) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (by exact_mod_cast (Nat.zero_le x))]
      congr 1
      norm_num

theorem rpow_lt_transitionSelbergHalfLevel_add_one (x : ℕ) :
    (x : ℝ) ^ ((1 : ℝ) / 20000) <
      transitionSelbergHalfLevel x + 1 := by
  unfold transitionSelbergHalfLevel
  exact_mod_cast Nat.lt_floor_add_one
    ((x : ℝ) ^ ((1 : ℝ) / 20000))

theorem transitionSelbergMass_cross_lower
    {C : ℝ} (hC : 0 < C)
    (hglobal : ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100))
    {x : ℕ} (hx : 1 < x) (hxEven : Even x)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    ((1 / 4) *
        Real.log (transitionSelbergHalfLevel x + 1)) ^ 2 ≤
      primeFactorEulerPenalty x *
        (C * (Real.log (transitionSelbergHalfLevel x + 2)) ^
          ((1 : ℝ) / 100)) *
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq)
          (transitionSelbergLevel x) := by
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hlogH :
      (1 / 4) * Real.log (Y + 1) ≤
        squarefreeHarmonic Y := by
    calc
      (1 / 4) * Real.log (Y + 1) ≤
          (1 / 4) * harmonicUpTo Y :=
        mul_le_mul_of_nonneg_left
          (log_add_one_le_harmonicUpTo Y) (by norm_num)
      _ ≤ squarefreeHarmonic Y :=
        quarter_harmonicUpTo_le_squarefreeHarmonic Y
  have hlogNonneg : 0 ≤ Real.log (Y + 1) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ Y + 1 by omega)
  have hsq :
      ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hlogNonneg) hlogH 2
  have hpair :=
    squarefreeHarmonic_sq_le_pairHarmonic
      hC hglobal (x := x) (Y := Y) (by omega)
  have hpairMass :=
    coprimePairHarmonic_le_truncatedSelbergMass
      hx hxEven hq
      (transitionSelbergHalfLevel_sq_le_level
        (show 1 ≤ x by omega))
      (transitionSelbergLevel_le_cutoff
        (show 1 ≤ x by omega))
  have hfactor :
      0 ≤ primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) := by
    apply mul_nonneg
    · unfold primeFactorEulerPenalty
      positivity
    · exact mul_nonneg hC.le
        (Real.rpow_nonneg
          (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ Y + 2 by omega))) _)
  calc
    ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 := hsq
    _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            coprimePairHarmonic x Y := hpair
    _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            truncatedSelbergMass s R :=
      mul_le_mul_of_nonneg_left hpairMass hfactor

/-- At the chosen level the Selberg normalization has essentially
dimension-two logarithmic size, uniformly in the admissible Chen pair. -/
theorem eventually_transitionSelbergMass_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hx : 1 < x, ∀ hxEven : Even x, ∀ q,
        ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (smoothingTransitionBoundingSieve x q
              hx hxEven hq)
            (transitionSelbergLevel x) := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_global_primeFactorEulerPenalty_bound
  let a : ℝ := (1 : ℝ) / 20000
  let b : ℝ := (1 : ℝ) / 100
  let c : ℝ := a ^ 2 / (32 * C)
  have ha : 0 < a := by
    dsimp only [a]
    norm_num
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, ?_⟩
  have hxlarge : ∀ᶠ x : ℕ in atTop, 2 ≤ x :=
    eventually_ge_atTop 2
  have hlogone : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 1)
  filter_upwards
      [hxlarge, hlogone,
        eventually_primeFactorEulerPenalty_le_log_rpow] with
      x hx2 hxlog1 hpen
  intro hx hxEven q hq
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  let L := Real.log x
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hx)
  have hYcast :
      (Y : ℝ) ≤ (x : ℝ) ^ a := by
    dsimp only [Y, a, transitionSelbergHalfLevel]
    exact Nat.floor_le (by positivity)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hrpowx : (x : ℝ) ^ a ≤ x := by
    exact Real.rpow_le_self_of_one_le hxR (by
      dsimp only [a]
      norm_num)
  have hYxR : (Y : ℝ) ≤ x := hYcast.trans hrpowx
  have hYx : Y ≤ x := by exact_mod_cast hYxR
  have hYlogUpper :
      Real.log (Y + 2) ≤ 2 * L := by
    have harg : (Y + 2 : ℕ) ≤ 2 * x := by omega
    have hlogmono :
        Real.log (Y + 2) ≤ Real.log (2 * x) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast harg
    have hlog2le : Real.log 2 ≤ L := by
      dsimp only [L]
      exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by norm_num))
        (Set.mem_Ioi.mpr (by exact_mod_cast (show 0 < x by omega)))
        (by exact_mod_cast hx2)
    calc
      Real.log (Y + 2) ≤ Real.log (2 * x) := hlogmono
      _ = Real.log 2 + L := by
        dsimp only [L]
        rw [Real.log_mul (by norm_num) (by exact_mod_cast (show x ≠ 0 by omega))]
      _ ≤ 2 * L := by linarith
  have hYpow :
      (Real.log (Y + 2)) ^ b ≤ 2 * L ^ b := by
    have hbase :
        (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ Y + 2 by omega))
      · exact hYlogUpper
      · exact hb.le
    have hmul :
        (2 * L) ^ b = (2 : ℝ) ^ b * L ^ b :=
      Real.mul_rpow (by norm_num) hL.le
    have htwo : (2 : ℝ) ^ b ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by
        dsimp only [b]
        norm_num)
    calc
      (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := hbase
      _ = (2 : ℝ) ^ b * L ^ b := hmul
      _ ≤ 2 * L ^ b :=
        mul_le_mul_of_nonneg_right htwo
          (Real.rpow_nonneg hL.le _)
  have hYlogLower :
      a * L ≤ Real.log (Y + 1) := by
    have hlt := rpow_lt_transitionSelbergHalfLevel_add_one x
    have hlogmono :
        Real.log ((x : ℝ) ^ a) ≤ Real.log (Y + 1) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos (by positivity) _)
      · exact Set.mem_Ioi.mpr (by positivity)
      · simpa only [Y, a] using hlt.le
    rw [Real.log_rpow (by positivity) a] at hlogmono
    simpa only [L] using hlogmono
  have hcross :=
    transitionSelbergMass_cross_lower
      hC hglobal hx hxEven hq
  have hmassPos : 0 < truncatedSelbergMass s R := by
    apply truncatedSelbergMass_pos
    exact one_le_transitionSelbergLevel (show 1 ≤ x by omega)
  have hpen' : primeFactorEulerPenalty x ≤ L ^ b := by
    simpa only [L, b] using hpen
  have hfactorUpper :
      primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) ≤
        2 * C * (L ^ b) ^ 2 := by
    calc
      primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) ≤
        L ^ b * (C * (Real.log (Y + 2)) ^ b) := by
          exact mul_le_mul_of_nonneg_right hpen'
            (mul_nonneg hC.le
              (Real.rpow_nonneg
                (Real.log_nonneg (by
                  exact_mod_cast (show 1 ≤ Y + 2 by omega))) _))
      _ ≤ L ^ b * (C * (2 * L ^ b)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hYpow hC.le)
            (Real.rpow_nonneg hL.le _)
      _ = 2 * C * (L ^ b) ^ 2 := by ring
  have hleftLower :
      ((a / 4) * L) ^ 2 ≤
        ((1 / 4) * Real.log (Y + 1)) ^ 2 := by
    apply pow_le_pow_left₀
    · positivity
    · calc
        (a / 4) * L = (1 / 4) * (a * L) := by ring
        _ ≤ (1 / 4) * Real.log (Y + 1) :=
          mul_le_mul_of_nonneg_left hYlogLower (by norm_num)
  have hcore :
      ((a / 4) * L) ^ 2 ≤
        (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := by
    calc
      ((a / 4) * L) ^ 2 ≤
          ((1 / 4) * Real.log (Y + 1)) ^ 2 := hleftLower
      _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) *
            truncatedSelbergMass s R := by
        simpa only [Y, R, s] using hcross
      _ ≤ (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R :=
        mul_le_mul_of_nonneg_right hfactorUpper hmassPos.le
  have hpowIdentity :
      L ^ (2 : ℕ) =
        (L ^ b) ^ 2 * L ^ ((99 : ℝ) / 50) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    congr 1
    dsimp only [b]
    norm_num
  have hscaled :
      (2 * C * (L ^ b) ^ 2) *
          (c * L ^ ((99 : ℝ) / 50)) ≤
        (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := by
    calc
      (2 * C * (L ^ b) ^ 2) *
          (c * L ^ ((99 : ℝ) / 50)) =
        ((a / 4) * L) ^ 2 := by
          dsimp only [c]
          calc
            (2 * C * (L ^ b) ^ 2) *
                (a ^ 2 / (32 * C) * L ^ ((99 : ℝ) / 50)) =
              (a ^ 2 / 16) *
                ((L ^ b) ^ 2 * L ^ ((99 : ℝ) / 50)) := by
                field_simp
                ring
            _ = (a ^ 2 / 16) * L ^ 2 := by rw [← hpowIdentity]
            _ = ((a / 4) * L) ^ 2 := by ring
      _ ≤ (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := hcore
  have hcoefPos : 0 < 2 * C * (L ^ b) ^ 2 := by positivity
  have h198 :
      c * L ^ ((99 : ℝ) / 50) ≤
        truncatedSelbergMass s R := by
    nlinarith [hscaled]
  have h197 :
      L ^ ((197 : ℝ) / 100) ≤
        L ^ ((99 : ℝ) / 50) := by
    apply Real.rpow_le_rpow_of_exponent_le hxlog1
    norm_num
  calc
    c * (Real.log x) ^ ((197 : ℝ) / 100) =
        c * L ^ ((197 : ℝ) / 100) := by rfl
    _ ≤ c * L ^ ((99 : ℝ) / 50) :=
      mul_le_mul_of_nonneg_left h197 hc.le
    _ ≤ truncatedSelbergMass s R := h198

/-- The explicit polynomial error at the chosen level has a fixed power
saving even after summing over the crude `x^(5/6)` bound for Chen pairs.
This purely asymptotic estimate is kept separate from the normalization
lower bound. -/
theorem eventually_transitionLevel_error_power_bound :
    ∀ᶠ x : ℕ in atTop,
      ((transitionSelbergLevel x : ℝ) *
          ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
        ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1) *
            (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x ≤
        (x : ℝ) ^ ((9 : ℝ) / 10) := by
  have hxone : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ x :=
    eventually_atTop.2 ⟨1, fun _ hx => by exact_mod_cast hx⟩
  have hlog :
      ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 1000) := by
    have hδ : (0 : ℝ) < (1 : ℝ) / 1000 := by norm_num
    have hreal :
        ∀ᶠ y : ℝ in atTop,
          ‖Real.log y ^ (1 : ℝ)‖ ≤
            ‖y ^ ((1 : ℝ) / 1000)‖ :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hδ).eventuallyLE
    have hnat :=
      tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat, eventually_gt_atTop 1] with x hx hx1
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx1)
    simpa [Real.norm_of_nonneg hlogpos.le,
      Real.norm_of_nonneg
        (Real.rpow_nonneg hxpos.le _)] using hx
  have hgap : (0 : ℝ) <
      (9 : ℝ) / 10 - (12527 : ℝ) / 15000 := by norm_num
  have hpowerReal :
      ∀ᶠ y : ℝ in atTop,
        2304 * y ^ ((12527 : ℝ) / 15000) ≤
          y ^ ((9 : ℝ) / 10) := by
    have hlarge :=
      (tendsto_rpow_atTop hgap).eventually
        (eventually_ge_atTop (2304 : ℝ))
    filter_upwards [hlarge, eventually_gt_atTop 0] with y hy hypos
    calc
      2304 * y ^ ((12527 : ℝ) / 15000) ≤
          y ^ ((9 : ℝ) / 10 - (12527 : ℝ) / 15000) *
            y ^ ((12527 : ℝ) / 15000) :=
        mul_le_mul_of_nonneg_right hy
          (Real.rpow_nonneg hypos.le _)
      _ = y ^ ((9 : ℝ) / 10) := by
        rw [← Real.rpow_add hypos]
        congr 1
        ring
  have hpower :
      ∀ᶠ x : ℕ in atTop,
        2304 * (x : ℝ) ^ ((12527 : ℝ) / 15000) ≤
          (x : ℝ) ^ ((9 : ℝ) / 10) :=
    tendsto_natCast_atTop_atTop.eventually hpowerReal
  filter_upwards [hxone, hlog, hpower] with x hx1 hlog hpower
  let R : ℝ := transitionSelbergLevel x
  have hR0 : 0 ≤ R := by positivity
  have hRle :
      R ≤ (x : ℝ) ^ ((1 : ℝ) / 10000) :=
    transitionSelbergLevel_cast_le_rpow x
  have hpow1 :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10000) :=
    Real.one_le_rpow hx1 (by norm_num)
  have hRadd :
      R + 1 ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10000) := by
    nlinarith
  have hNatAdd :
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ≤
        2 * (x : ℝ) ^ ((1 : ℝ) / 10000) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact hRadd
  have hthree :
      3 * R ^ 2 + 1 ≤
        4 * ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 := by
    have hsq :
        R ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 :=
      (sq_le_sq₀ hR0 (Real.rpow_nonneg (by positivity) _)).2 hRle
    nlinarith [hpow1]
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans_le hx1
  let X : ℝ := (x : ℝ) ^ ((1 : ℝ) / 10000)
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hRR :
      R * (R + 1) ≤ 2 * X ^ 2 := by
    dsimp only [X]
    calc
      R * (R + 1) ≤
          (x : ℝ) ^ ((1 : ℝ) / 10000) *
            (2 * (x : ℝ) ^ ((1 : ℝ) / 10000)) :=
        mul_le_mul hRle hRadd (by positivity) (by positivity)
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 := by ring
  have hfirst :
      (R * (R + 1)) ^ 2 ≤ 4 * X ^ 4 := by
    have hsquare :=
      pow_le_pow_left₀ (mul_nonneg hR0 (by positivity)) hRR 2
    nlinarith [sq_nonneg (X ^ 2)]
  have hsecond :
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 ≤
        4 * X ^ 2 := by
    have hsquare :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        (transitionSelbergLevel x + 1 : ℕ)) hNatAdd 2
    dsimp only [X]
    nlinarith [sq_nonneg ((x : ℝ) ^ ((1 : ℝ) / 10000))]
  have hthird :
      3 * R ^ 2 + 1 ≤ 4 * X ^ 2 := by
    simpa only [X] using hthree
  have hrpowmul :
      ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
          (x : ℝ) ^ ((5 : ℝ) / 6) *
            (x : ℝ) ^ ((1 : ℝ) / 1000) =
        (x : ℝ) ^ ((12527 : ℝ) / 15000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
      ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    congr 1
    norm_num
  calc
    (R * (R + 1)) ^ 2 *
          ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
            (3 * R ^ 2 + 1) *
              (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                Real.log x ≤
        2304 *
          (((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
            (x : ℝ) ^ ((5 : ℝ) / 6) *
              (x : ℝ) ^ ((1 : ℝ) / 1000)) := by
      calc
        (R * (R + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * R ^ 2 + 1) *
                  (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                    Real.log x ≤
            (4 * X ^ 4) * (4 * X ^ 2) * (4 * X ^ 2) *
              (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                ((x : ℝ) ^ ((1 : ℝ) / 1000)) := by
          gcongr
        _ = 576 * (X ^ 8 *
              (x : ℝ) ^ ((5 : ℝ) / 6) *
                (x : ℝ) ^ ((1 : ℝ) / 1000)) := by ring
        _ ≤ 2304 * (((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
              (x : ℝ) ^ ((5 : ℝ) / 6) *
                (x : ℝ) ^ ((1 : ℝ) / 1000)) := by
          dsimp only [X]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 2304 * (x : ℝ) ^ ((12527 : ℝ) / 15000) := by
      rw [hrpowmul]
    _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := hpower

/-- The optimized upper-bound sieve, normalized by the uniform lower
bound for `G(R)`, applied to one admissible prime pair. -/
theorem smoothingBoundaryLargeBase_pair_le
    {x : ℕ} {q : ℕ × ℕ} {c : ℝ}
    (hx : 2 ≤ x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hc : 0 < c)
    (hmass :
      c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q
            (by omega) hxEven hq)
          (transitionSelbergLevel x)) :
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (smoothingBoundaryIndices x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
      3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
  let s :=
    smoothingTransitionBoundingSieve x q (by omega) hxEven hq
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  let W : ℝ :=
    (smoothingTransitionUpper x q -
      smoothingTransitionLower x q : ℕ)
  have hR : 1 ≤ transitionSelbergLevel x :=
    one_le_transitionSelbergLevel (by omega)
  have hinner :=
    smoothingBoundaryLargeBase_inner_le_siftedCard hx q
  have hsieve :=
    smoothingTransitionSifted_card_le_optimal
      (x := x) (q := q) (R := transitionSelbergLevel x)
      (by omega) hxEven hq hR
  dsimp only at hsieve
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hleftPos :
      0 < c * (Real.log x) ^ ((197 : ℝ) / 100) := by
    positivity
  have hGpos :
      0 < truncatedSelbergMass s (transitionSelbergLevel x) :=
    truncatedSelbergMass_pos s hR
  have hinv :
      (truncatedSelbergMass s
          (transitionSelbergLevel x))⁻¹ ≤
        (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ :=
    (inv_le_inv₀ hGpos hleftPos).2 (by
      simpa only [s] using hmass)
  have hpairLog :=
    pairLog_inv_mul_log_le_three
      (show 1 < x by omega) hq
  have hweight0 :
      0 ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
    have hY := one_lt_pairQuotient hq
    exact inv_nonneg.mpr (Real.log_nonneg hY.le)
  have hmain0 :
      0 ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s
            (transitionSelbergLevel x))⁻¹ + E := by
    dsimp only [E]
    positivity
  calc
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (smoothingBoundaryIndices x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (smoothingTransitionSiftedIndices x q).card) := by
      gcongr
    _ ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E)) := by
      gcongr
    _ =
        ((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          Real.log x) *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E) := by ring
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (truncatedSelbergMass s
              (transitionSelbergLevel x))⁻¹ + E) :=
      mul_le_mul_of_nonneg_right hpairLog hmain0
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
            E) := by
      gcongr
    _ = 3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
      rfl

theorem smoothingBoundaryLargeBaseMass_le_explicit
    {x : ℕ} {c : ℝ} (hx : 2 ≤ x) (hxEven : Even x)
    (hc : 0 < c)
    (hmass :
      ∀ q, ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (smoothingTransitionBoundingSieve x q
              (by omega) hxEven hq)
            (transitionSelbergLevel x)) :
    smoothingBoundaryLargeBaseMass x ≤
      3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
  unfold smoothingBoundaryLargeBaseMass
  let A : ℝ :=
    (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n =>
                ¬(n.minFac : ℝ) ≤
                  (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
        ∑ q ∈ chenPairs x,
          3 *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) * A + E) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [A, E] using
        smoothingBoundaryLargeBase_pair_le
          hx hxEven hq hc (hmass q hq)
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) * A +
          ((chenPairs x).card : ℝ) * E) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
      rfl

/-- The large-base part of the smoothing boundary has the logarithmic
saving required in Lemma 5. -/
theorem eventually_smoothingBoundaryLargeBaseMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothingBoundaryLargeBaseMass x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨c, hc, hmass⟩ :=
    eventually_transitionSelbergMass_lower
  let C : ℝ := 3 * (13 * c⁻¹ + 1)
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have hpowFiveSixths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 6) (r := (2.01 : ℝ)) (by norm_num)
  have hpowNineTenths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ)) (by norm_num)
  filter_upwards [hmass, eventually_transition_width_small,
      eventually_sum_inv_primesLE_sq_le_log_rpow,
      eventually_transitionLevel_error_power_bound,
      hpowFiveSixths, hpowNineTenths,
      eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop 1)] with
      x hmass hsmall hprime herr hpowFiveSixths
        hpowNineTenths hx hL
  intro hxEven
  let L : ℝ := Real.log x
  let P : ℝ := ∑ p ∈ x.primesLE, (p : ℝ)⁻¹
  let A : ℝ := (c * L ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  let Q : ℝ := ((chenPairs x).card : ℝ)
  let T : ℝ :=
    (x : ℝ) / (Real.log x) ^ (2.01 : ℝ)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hL
  have hLone : 1 ≤ L := by
    simpa only [L, Function.comp_apply] using hL
  have hP : P ^ 2 ≤ L ^ ((1 : ℝ) / 25) := by
    simpa only [P, L] using hprime
  have hQ : Q ≤ 9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
    dsimp only [Q]
    exact chenPairs_card_cast_le x (by omega)
  have hwidth :=
    sum_smoothingTransition_width_le (x := x) hsmall
  have hexplicit :=
    smoothingBoundaryLargeBaseMass_le_explicit
      hx hxEven hc (fun q hq =>
        hmass (show 1 < x by omega) hxEven q hq)
  have hAeq :
      A = c⁻¹ * L ^ (-(197 : ℝ) / 100) := by
    dsimp only [A]
    rw [mul_inv, ← Real.rpow_neg hLpos.le]
    congr 2
    ring
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hAle : A ≤ c⁻¹ := by
    have hpowOne :
        1 ≤ L ^ ((197 : ℝ) / 100) :=
      Real.one_le_rpow hL (by norm_num)
    have hbase :
        c ≤ c * L ^ ((197 : ℝ) / 100) := by
      nlinarith [mul_le_mul_of_nonneg_left hpowOne hc.le]
    dsimp only [A]
    exact (inv_le_inv₀ (mul_pos hc (by positivity)) hc).2 hbase
  have hpowCombine :
      L ^ (-(0.1 : ℝ)) *
          L ^ ((1 : ℝ) / 25) *
            L ^ (-(197 : ℝ) / 100) =
        L ^ (-(203 : ℝ) / 100) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1
    norm_num
  have hlogPower :
      L ^ (-(203 : ℝ) / 100) ≤
        (L ^ (2.01 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hLpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hL
    norm_num
  have hmainShort :
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
        4 * c⁻¹ * T := by
    calc
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
          4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) *
            L ^ ((1 : ℝ) / 25) * A := by
        gcongr
      _ = 4 * c⁻¹ * (x : ℝ) *
          L ^ (-(203 : ℝ) / 100) := by
        rw [hAeq, ← hpowCombine]
        ring
      _ ≤ 4 * c⁻¹ * (x : ℝ) *
          (L ^ (2.01 : ℝ))⁻¹ := by
        gcongr
      _ = 4 * c⁻¹ * T := by
        dsimp only [T, L]
        rw [div_eq_mul_inv]
        ring
  have hcardMain :
      Q * A ≤ 9 * c⁻¹ * T := by
    calc
      Q * A ≤
          (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * c⁻¹ := by
        gcongr
      _ = 9 * c⁻¹ * (x : ℝ) ^ ((5 : ℝ) / 6) := by ring
      _ ≤ 9 * c⁻¹ * T := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [T]
          simpa only [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num]
            using hpowFiveSixths
        · positivity
  have herror :
      Q * E ≤ T := by
    have hQE :
        Q * E * L ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E * L ≤
            (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * E * L := by
          gcongr
        _ = E * (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := by
          dsimp only [L]
          ring
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
          simpa only [E] using herr
    have hQE0 : 0 ≤ Q * E := by
      dsimp only [Q, E]
      positivity
    have hdrop : Q * E ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E = Q * E * 1 := by ring
        _ ≤ Q * E * L :=
          mul_le_mul_of_nonneg_left hLone hQE0
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := hQE
    have hp :
        (x : ℝ) ^ ((9 : ℝ) / 10) ≤ T := by
      dsimp only [T]
      simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num]
        using hpowNineTenths
    exact hdrop.trans hp
  have hwidthA :
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
        (4 * c⁻¹ + 9 * c⁻¹) * T := by
    calc
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
          (4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 + Q) *
            A := by
        gcongr
      _ = 4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A +
          Q * A := by ring
      _ ≤ 4 * c⁻¹ * T + 9 * c⁻¹ * T :=
        add_le_add hmainShort hcardMain
      _ = (4 * c⁻¹ + 9 * c⁻¹) * T := by ring
  calc
    smoothingBoundaryLargeBaseMass x ≤
        3 *
          ((∑ q ∈ chenPairs x,
              ((smoothingTransitionUpper x q -
                  smoothingTransitionLower x q : ℕ) : ℝ)) * A +
            Q * E) := by
      simpa only [A, E, Q, L] using hexplicit
    _ ≤ 3 * (((4 * c⁻¹ + 9 * c⁻¹) * T) + T) := by
      gcongr
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C, T]
      ring

end Chen
