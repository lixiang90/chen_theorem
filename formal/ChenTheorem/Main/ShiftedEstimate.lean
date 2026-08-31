import ChenTheorem.MainEstimates
import ChenTheorem.Main.ShiftedSieveLemmas
import ChenTheorem.Main.ShiftedLemma5
import ChenTheorem.Main.ShiftedLemma5Boundary
import ChenTheorem.Main.ShiftedLemma5Arithmetic
import ChenTheorem.Main.ShiftedKeyInequality

open Filter Real
open scoped Classical

namespace Chen

/-!
The nine shifted lemmas and the fixed-shift analogue of inequality (28) are
assembled here.  First the numerical gap is proved on even scale parameters;
then a one-step even-floor comparison removes that auxiliary parity condition.
-/

/-- The `x^0.91` exceptional loss is negligible against the fixed-shift main
term, with an arbitrary positive coefficient. -/
theorem eventually_shifted_rpow_091_le_singular_error
    (h : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (0.91 : ℝ) ≤
        δ * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 := by
  let k : ℝ := δ * twinConst
  have hk : 0 < k := by
    dsimp only [k]
    exact mul_pos hδ twinConst_pos
  have hlogReal :
      ∀ᶠ y : ℝ in atTop,
        ‖Real.log y ^ (2 : ℝ)‖ ≤ k * ‖y ^ (0.09 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop
      (2 : ℝ) (by norm_num : (0 : ℝ) < 0.09)).def hk
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlogReal
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hlogNat, hlogOne, eventually_ge_atTop 1] with
      x hlog hlogOne hx
  have hxpos : (0 : ℝ) < x :=
    zero_lt_one.trans_le (by exact_mod_cast hx)
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogOne
  have hlogsq :
      Real.log (x : ℝ) ^ 2 ≤ k * (x : ℝ) ^ (0.09 : ℝ) := by
    simpa [Real.rpow_natCast,
      Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hlog
  have hpow :
      (x : ℝ) ^ (0.91 : ℝ) * (x : ℝ) ^ (0.09 : ℝ) = x := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsmall :
      (x : ℝ) ^ (0.91 : ℝ) ≤
        k * (x : ℝ) / Real.log (x : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).2
    calc
      (x : ℝ) ^ (0.91 : ℝ) * Real.log (x : ℝ) ^ 2 ≤
          (x : ℝ) ^ (0.91 : ℝ) *
            (k * (x : ℝ) ^ (0.09 : ℝ)) := by gcongr
      _ = k * ((x : ℝ) ^ (0.91 : ℝ) *
          (x : ℝ) ^ (0.09 : ℝ)) := by ring
      _ = k * (x : ℝ) := by rw [hpow]
  calc
    (x : ℝ) ^ (0.91 : ℝ) ≤
        k * (x : ℝ) / Real.log (x : ℝ) ^ 2 := hsmall
    _ ≤ δ * (x : ℝ) * chenConst h /
          Real.log (x : ℝ) ^ 2 := by
      dsimp only [k]
      have hden : 0 ≤ (Real.log (x : ℝ) ^ 2)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        δ * twinConst * (x : ℝ) * (Real.log (x : ℝ) ^ 2)⁻¹ =
          δ * (x : ℝ) * twinConst * (Real.log (x : ℝ) ^ 2)⁻¹ := by ring
        _ ≤ δ * (x : ℝ) * chenConst h *
            (Real.log (x : ℝ) ^ 2)⁻¹ := by
          gcongr
          exact twinConst_le_chenConst h

/-- Quantitative fixed-shift estimate on the auxiliary even scales, retaining
enough numerical slack to pass to every natural scale. -/
theorem chenCountShift_lower_even
    (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    ∀ᶠ x : ℕ in atTop, Even x →
      0.6705 * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 ≤
        (chenCountShift h x : ℝ) := by
  filter_upwards [shifted_key_inequality h h0 hh,
      shiftedSieved_lower_bound h h0 hh,
      shiftedSieveOmega_le h h0 hh,
      eventually_shifted_rpow_091_le_singular_error
        h 0.0001 (by norm_num)] with
      x hkey hlower homega herror
  intro hxEven
  have hkey' := hkey hxEven
  have hlower' := hlower hxEven
  have homega' := homega hxEven
  let B : ℝ :=
    (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2
  have hOmegaHalf : (shiftedSieveOmega h x : ℝ) / 2 ≤ 1.9702 * B := by
    dsimp only [B]
    ring_nf at homega' ⊢
    linarith
  have herror' : (x : ℝ) ^ (0.91 : ℝ) ≤ 0.0001 * B := by
    calc
      (x : ℝ) ^ (0.91 : ℝ) ≤
          0.0001 * (x : ℝ) * chenConst h /
            Real.log (x : ℝ) ^ 2 := herror
      _ = 0.0001 * B := by
        dsimp only [B]
        ring
  dsimp only [B] at hkey' hlower' hOmegaHalf herror' ⊢
  ring_nf at hkey' hlower' hOmegaHalf herror' ⊢
  linarith

/-- Largest even natural number not exceeding `x`. -/
def shiftedEvenFloor (x : ℕ) : ℕ := 2 * (x / 2)

theorem shiftedEvenFloor_even (x : ℕ) : Even (shiftedEvenFloor x) := by
  exact ⟨x / 2, by simp [shiftedEvenFloor, two_mul]⟩

theorem shiftedEvenFloor_le (x : ℕ) : shiftedEvenFloor x ≤ x := by
  unfold shiftedEvenFloor
  omega

theorem le_shiftedEvenFloor_add_one (x : ℕ) :
    x ≤ shiftedEvenFloor x + 1 := by
  have hmod := Nat.mod_lt x (by norm_num : 0 < 2)
  have hdecomp := Nat.mod_add_div x 2
  unfold shiftedEvenFloor
  omega

theorem tendsto_shiftedEvenFloor_atTop :
    Tendsto shiftedEvenFloor atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b + 1, ?_⟩
  intro x hx
  have hclose := le_shiftedEvenFloor_add_one x
  omega

theorem chenCountShift_mono_right
    (h : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    chenCountShift h x ≤ chenCountShift h y := by
  unfold chenCountShift
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hpData.1
    omega), hpData.2⟩

/-- Quantitative shifted form used for Theorem 2. -/
theorem chenCountShift_lower_estimate
    (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    ∀ᶠ x : ℕ in atTop,
      0.67 * (x : ℝ) * chenConst h / (Real.log x) ^ 2 ≤
        (chenCountShift h x : ℝ) := by
  let y : ℕ → ℕ := shiftedEvenFloor
  have hyT : Tendsto y atTop atTop := tendsto_shiftedEvenFloor_atTop
  have hlower := hyT.eventually (chenCountShift_lower_even h hh h0)
  have hyLarge := hyT.eventually (eventually_ge_atTop 2000)
  filter_upwards [hlower, hyLarge] with x hlower hyLarge
  have hyEven : Even (y x) := shiftedEvenFloor_even x
  have hyx : y x ≤ x := shiftedEvenFloor_le x
  have hxyClose : x ≤ y x + 1 := le_shiftedEvenFloor_add_one x
  have hy1 : 1 < y x := by omega
  have hx1 : 1 < x := hy1.trans_le hyx
  have hlogy : 0 < Real.log (y x : ℝ) :=
    Real.log_pos (by exact_mod_cast hy1)
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx1)
  have hlogle : Real.log (y x : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hyx)
  have hlogsq : Real.log (y x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ 2 := by
    nlinarith
  have hxyScale : (x : ℝ) ≤ 1.0005 * (y x : ℝ) := by
    have hclose : (x : ℝ) ≤ (y x : ℝ) + 1 := by exact_mod_cast hxyClose
    have hyLargeReal : (2000 : ℝ) ≤ y x := by exact_mod_cast hyLarge
    nlinarith
  have hratio :
      (x : ℝ) / Real.log (x : ℝ) ^ 2 ≤
        1.0005 * (y x : ℝ) / Real.log (y x : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hlogx) (sq_pos_of_pos hlogy)]
    calc
      (x : ℝ) * Real.log (y x : ℝ) ^ 2 ≤
          (1.0005 * (y x : ℝ)) * Real.log (y x : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hxyScale (sq_nonneg _)
      _ ≤ (1.0005 * (y x : ℝ)) * Real.log (x : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hlogsq (by positivity)
  have hconst : 0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  have hmainCompare :
      0.67 * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 ≤
        0.6705 * (y x : ℝ) * chenConst h /
          Real.log (y x : ℝ) ^ 2 := by
    calc
      0.67 * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 =
          (0.67 * chenConst h) *
            ((x : ℝ) / Real.log (x : ℝ) ^ 2) := by ring
      _ ≤ (0.67 * chenConst h) *
          (1.0005 * (y x : ℝ) / Real.log (y x : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ 0.6705 * (y x : ℝ) * chenConst h /
          Real.log (y x : ℝ) ^ 2 := by
        have hbase :
            0 ≤ (y x : ℝ) * chenConst h /
              Real.log (y x : ℝ) ^ 2 := by positivity
        calc
          (0.67 * chenConst h) *
              (1.0005 * (y x : ℝ) /
                Real.log (y x : ℝ) ^ 2) =
            (0.67 * 1.0005) *
              ((y x : ℝ) * chenConst h /
                Real.log (y x : ℝ) ^ 2) := by ring
          _ ≤ 0.6705 *
              ((y x : ℝ) * chenConst h /
                Real.log (y x : ℝ) ^ 2) := by
            gcongr
            norm_num
          _ = 0.6705 * (y x : ℝ) * chenConst h /
              Real.log (y x : ℝ) ^ 2 := by ring
  calc
    0.67 * (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 ≤
        0.6705 * (y x : ℝ) * chenConst h /
          Real.log (y x : ℝ) ^ 2 := hmainCompare
    _ ≤ (chenCountShift h (y x) : ℝ) := hlower hyEven
    _ ≤ (chenCountShift h x : ℝ) := by
      exact_mod_cast chenCountShift_mono_right h hyx

end Chen
