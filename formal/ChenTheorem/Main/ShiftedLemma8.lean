import ChenTheorem.Main.ShiftedLemma7Normalization

open Filter Real
open scoped Classical

namespace Chen

/-! # Fixed-shift analogue of Lemma 8

The prime-pair kernel is independent of the additive shift, so the two
partial-summation estimates and the numerical integral (24) are reused
verbatim.  Only the absorption of the logarithmic error is restated with the
fixed singular series `chenConst h`.
-/

/-- A logarithmic error is eventually absorbed by any positive multiple of
the fixed-shift singular main term. -/
theorem eventually_shifted_log_error_le_singular
    (h : ℕ) (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) ≤
        δ * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 := by
  let T : ℝ := C / (δ * twinConst)
  have hden : 0 < δ * twinConst := mul_pos hδ twinConst_pos
  have hT : 0 < T := div_pos hC hden
  have htendsto :
      Tendsto (fun y : ℝ => (Real.log y) ^ (0.01 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).comp
      Real.tendsto_log_atTop
  have hlargeReal :
      ∀ᶠ y : ℝ in atTop, T ≤ (Real.log y) ^ (0.01 : ℝ) :=
    htendsto.eventually (eventually_ge_atTop T)
  have hlarge := tendsto_natCast_atTop_atTop.eventually hlargeReal
  filter_upwards [hlarge, eventually_gt_atTop 1] with x hlarge hx
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hlogSmallPos : 0 < Real.log (x : ℝ) ^ (0.01 : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hfactor :
      C ≤ δ * chenConst h * Real.log (x : ℝ) ^ (0.01 : ℝ) := by
    calc
      C = δ * twinConst * T := by
        dsimp only [T]
        field_simp [twinConst_pos.ne']
      _ ≤ δ * twinConst * Real.log (x : ℝ) ^ (0.01 : ℝ) := by
        gcongr
      _ ≤ δ * chenConst h * Real.log (x : ℝ) ^ (0.01 : ℝ) := by
        gcongr
        exact twinConst_le_chenConst h
  have hlogSplit :
      Real.log (x : ℝ) ^ (2.01 : ℝ) =
        Real.log (x : ℝ) ^ 2 * Real.log (x : ℝ) ^ (0.01 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hlogpos]
    norm_num
  rw [hlogSplit]
  calc
    C * (x : ℝ) /
        (Real.log (x : ℝ) ^ 2 *
          Real.log (x : ℝ) ^ (0.01 : ℝ)) =
      (C / Real.log (x : ℝ) ^ (0.01 : ℝ)) *
        ((x : ℝ) / Real.log (x : ℝ) ^ 2) := by
          field_simp
    _ ≤ (δ * chenConst h) *
        ((x : ℝ) / Real.log (x : ℝ) ^ 2) := by
      gcongr
      exact (div_le_iff₀ hlogSmallPos).2 hfactor
    _ = δ * (x : ℝ) * chenConst h /
        Real.log (x : ℝ) ^ 2 := by ring

/-- **Shifted Lemma 8**: for every fixed positive even shift `h`, the weighted
upper-bound sieve has the same numerical constant as in the original lemma. -/
theorem shiftedSieveOmega_le
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (shiftedSieveOmega h x : ℝ) ≤
        3.9404 * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 := by
  let ε : ℝ := 0.000001
  have hε : 0 < ε := by norm_num [ε]
  have hε' : ε < 1 / 100 := by norm_num [ε]
  obtain ⟨C, hC, hOmega⟩ :=
    shiftedSieveOmega_le_mOne h hh0 hhEven ε hε hε'
  have hmOne := shiftedMOne_le h hh0 hhEven ε hε hε'
  have herror :=
    eventually_shifted_log_error_le_singular
      h C 0.00005 hC (by norm_num)
  filter_upwards [hOmega, hmOne, chenPairs_kernel_le,
      herror, eventually_gt_atTop 1] with
      x hOmega hmOne hkernel herror hx
  intro hxEven
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst : 0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  let A : ℝ :=
    (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 - ε := sub_pos.mpr (hε'.trans (by norm_num))
  have hmOne' := hmOne hxEven
  have hmain :
      shiftedMOne h x ε / (1 - ε) ≤
        ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A := by
    calc
      shiftedMOne h x ε / (1 - ε) ≤
          ((8 + 24 * ε) * (x : ℝ) * chenConst h /
              Real.log (x : ℝ) *
            ∑ q ∈ chenPairs x,
              ((q.1 : ℝ) * (q.2 : ℝ) *
                Real.log ((x : ℝ) /
                  ((q.1 : ℝ) * q.2)))⁻¹) /
            (1 - ε) :=
        (div_le_div_iff_of_pos_right hden).2 hmOne'
      _ ≤ (((8 + 24 * ε) * (x : ℝ) * chenConst h /
              Real.log (x : ℝ)) *
            (0.492541 / Real.log (x : ℝ))) /
            (1 - ε) := by
        gcongr
      _ = ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A := by
        dsimp only [A]
        field_simp
  have hOmega' := hOmega hxEven
  have herror' :
      C * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) ≤
        0.00005 * A := by
    dsimp only [A]
    convert herror using 1
    ring
  have hnumeric :
      (8 + 24 * ε) * 0.492541 / (1 - ε) +
          0.00005 ≤ 3.9404 := by
    norm_num [ε]
  calc
    (shiftedSieveOmega h x : ℝ) ≤
        shiftedMOne h x ε / (1 - ε) +
          C * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := hOmega'
    _ ≤ ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A +
          0.00005 * A := add_le_add hmain herror'
    _ = (((8 + 24 * ε) * 0.492541 / (1 - ε)) +
          0.00005) * A := by ring
    _ ≤ 3.9404 * A := by gcongr
    _ = 3.9404 * (x : ℝ) * chenConst h /
          Real.log (x : ℝ) ^ 2 := by
      dsimp only [A]
      ring

end Chen
