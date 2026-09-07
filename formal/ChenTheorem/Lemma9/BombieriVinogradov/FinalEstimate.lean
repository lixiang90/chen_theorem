import ChenTheorem.Lemma9.BombieriVinogradov.AsymptoticAssembly
import ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorEstimate

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Final Bombieri--Vinogradov estimate

This file joins the independently proved large-conductor Vaughan estimate
and the small-conductor Siegel--Walfisz estimate.  The first step below
specializes the latter to the common integer polylogarithmic cutoff.
-/

/-- At the standard Vaughan cutoff, the small primitive-conductor mean has
an arbitrary inverse-logarithmic saving. -/
theorem primitiveAdjustedMean_bvPolylogCutoff_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (A B : ℕ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      primitiveAdjustedMean x 0 (bvPolylogCutoff (2 * B) x) ≤
        C * (x : ℝ) / Real.log (x : ℝ) ^ A := by
  let R : ℕ := 2 * B + 1
  obtain ⟨C, hC, hsmall⟩ :=
    primitiveAdjustedMean_smallConductor_bound hzf (A + R) R (by
      dsimp only [R]
      omega)
  refine ⟨C, hC, ?_⟩
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall, eventually_ge_atTop 2,
      hlogT.eventually (eventually_ge_atTop (3 ^ (2 * B) : ℝ)),
      hlogT.eventually (eventually_ge_atTop 1)] with
      x hsmall hx hlogLarge hlogOne
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hcutBasic : (bvPolylogCutoff (2 * B) x : ℝ) ≤
      3 ^ (2 * B) * L ^ (2 * B) := by
    dsimp only [L]
    exact bvPolylogCutoff_cast_le (2 * B) (by omega) hlogOne
  have hcut : (bvPolylogCutoff (2 * B) x : ℝ) ≤ L ^ R := by
    calc
      (bvPolylogCutoff (2 * B) x : ℝ) ≤
          3 ^ (2 * B) * L ^ (2 * B) := hcutBasic
      _ ≤ L * L ^ (2 * B) := by gcongr
      _ = L ^ R := by
        dsimp only [R]
        rw [pow_succ']
  have hraw := hsmall (bvPolylogCutoff (2 * B) x) hcut
  calc
    primitiveAdjustedMean x 0 (bvPolylogCutoff (2 * B) x) ≤
        C * (bvPolylogCutoff (2 * B) x : ℝ) * (x : ℝ) /
          L ^ (A + R) := by simpa only [L] using hraw
    _ ≤ C * L ^ R * (x : ℝ) / L ^ (A + R) := by
      gcongr
    _ = C * (x : ℝ) / L ^ A := by
      rw [pow_add]
      field_simp
      ring

/-- The power-saving Type-I contribution absorbs every fixed logarithmic
loss after multiplication by the outer harmonic factor. -/
theorem eventually_typeI_final_term_le
    (C₂ : ℝ) (B A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      12 * Real.log (x : ℝ) ^ 3 * bvTypeIMajorant C₂ B x ≤
        (x : ℝ) / Real.log (x : ℝ) ^ A := by
  let D : ℝ := 12 * (200 * (C₂ + 1) * 3 ^ (4 * B))
  have habsorb := Chen.eventually_const_mul_log_pow_le_rpow
    D (4 * B + 9 + A) (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [habsorb, eventually_ge_atTop 2] with x habsorb hx
  let L : ℝ := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [le_div_iff₀ (pow_pos hLpos A)]
  calc
    (12 * Real.log (x : ℝ) ^ 3 * bvTypeIMajorant C₂ B x) *
          Real.log (x : ℝ) ^ A =
        (D * L ^ (4 * B + 9 + A)) *
          (x : ℝ) ^ ((3 : ℝ) / 4) := by
      unfold bvTypeIMajorant
      dsimp only [D, L]
      rw [show 4 * B + 9 + A = 3 + (4 * B + 6) + A by omega,
        pow_add, pow_add]
      ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4) *
          (x : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num

/-- Integer-exponent form of Bombieri--Vinogradov.  This is the form in
which all logarithmic powers from the Vaughan decomposition are assembled. -/
theorem bombieriVinogradov_nat
    (hzf : Chen.PrimitiveZeroFreeRegion) (A : ℕ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B →
          (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ A := by
  let B : ℕ := A + 10
  have hB : 1 ≤ B := by dsimp only [B]; omega
  obtain ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
      hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, hreduce⟩ :=
    sum_maxProgressionError_polylog_reduction
  obtain ⟨Cₛ, hCₛ, hsmall⟩ :=
    primitiveAdjustedMean_bvPolylogCutoff_bound hzf (A + 2) B hB
  let D : ℝ :=
    9 * Real.sqrt (672 * (2 * Cᵢ₀ ^ 2 * Cᵢ₁)) +
      360 * Real.sqrt (672 * (2 * Cᵦ₀ ^ 2 * Cᵦ₁))
  let C : ℝ := 4 * Cₛ + 1 + 12 * D + 12
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have htypeI := eventually_typeI_final_term_le C₂ B A
  have hcutLevel := eventually_bvPolylogCutoff_le_level_self B
  have hcutSq := eventually_bvPolylogCutoff_sq_le (2 * B)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hsmall, htypeI, hcutLevel, hcutSq,
      eventually_ge_atTop 2,
      hlogT.eventually (eventually_ge_atTop 1)] with
      x hsmall htypeI hcutLevel hcutSq hx hlogOne
  intro Q hQ
  let P : ℕ := bvPolylogCutoff (2 * B) x
  let Q' : ℕ := max Q P
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hPpos : 1 ≤ P := by
    dsimp only [P]
    exact bvPolylogCutoff_pos (2 * B) x
  have hQ'pos : 1 ≤ Q' := hPpos.trans (Nat.le_max_right Q P)
  have hPQ' : P ≤ Q' := Nat.le_max_right Q P
  have hQ'level : (Q' : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
    have hQcast : (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
      simpa only [L] using hQ
    have hPcast : (P : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
      simpa only [P, L] using hcutLevel
    by_cases hQP : Q ≤ P
    · rw [show Q' = P by dsimp only [Q']; exact max_eq_right hQP]
      exact hPcast
    · rw [show Q' = Q by
          dsimp only [Q']
          exact max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hQP))]
      exact hQcast
  have hcutTwo : 2 ≤ P ^ 2 := by
    dsimp only [P]
    exact bvPolylogCutoff_sq_two_le B x hB hx
  have hreduction := hreduce B x Q' hx hQ'pos hlogOne
    (by simpa only [L] using hQ'level) hPQ' hcutTwo
    (by simpa only [P] using hcutSq)
  have hsubset : Finset.Icc 1 Q ⊆ Finset.Icc 1 Q' := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
      (Finset.mem_Icc.mp hq).2.trans (Nat.le_max_left Q P)⟩
  have hmono :
      (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
        ∑ q ∈ Finset.Icc 1 Q', maxProgressionError x q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ => maxProgressionError_nonneg x q)
  have hsmallTerm :
      4 * L ^ 2 * primitiveAdjustedMean x 0 P ≤
        (4 * Cₛ) * (x : ℝ) / L ^ A := by
    calc
      4 * L ^ 2 * primitiveAdjustedMean x 0 P ≤
          4 * L ^ 2 * (Cₛ * (x : ℝ) / L ^ (A + 2)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [P, L] using hsmall) (by positivity)
      _ = (4 * Cₛ) * (x : ℝ) / L ^ A := by
        rw [pow_add]
        field_simp
  have htypeII :
      12 * L ^ 3 * bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x ≤
        (12 * D) * (x : ℝ) / L ^ A := by
    have hX : 0 ≤ 12 * D * (x : ℝ) := by positivity
    have hp := mul_pow_mul_inv_pow_le_div_pow hX hlogOne
      (p := 9) (n := B) (k := A) (by dsimp only [B]; omega)
    unfold bvTypeIIMajorant
    dsimp only [D, L] at hp ⊢
    rw [div_eq_mul_inv]
    convert hp using 1
    ring
  have herror :
      12 * (x : ℝ) * L ^ 2 / L ^ (2 * B) ≤
        12 * (x : ℝ) / L ^ A := by
    have hX : 0 ≤ 12 * (x : ℝ) := by positivity
    have hp := mul_pow_mul_inv_pow_le_div_pow hX hlogOne
      (p := 2) (n := 2 * B) (k := A) (by dsimp only [B]; omega)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hp
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
        ∑ q ∈ Finset.Icc 1 Q', maxProgressionError x q := hmono
    _ ≤ 4 * L ^ 2 * primitiveAdjustedMean x 0 P +
          12 * L ^ 3 *
            (bvTypeIMajorant C₂ B x +
              bvTypeIIMajorant Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ B x) +
          12 * (x : ℝ) * L ^ 2 / L ^ (2 * B) := by
      simpa only [P, L] using hreduction
    _ ≤ (4 * Cₛ) * (x : ℝ) / L ^ A +
          ((x : ℝ) / L ^ A + (12 * D) * (x : ℝ) / L ^ A) +
          12 * (x : ℝ) / L ^ A := by
      rw [mul_add]
      exact add_le_add (add_le_add hsmallTerm (add_le_add htypeI htypeII)) herror
    _ = C * (x : ℝ) / L ^ A := by
      dsimp only [C]
      ring

/-- Classical Bombieri--Vinogradov at level `1/2`, conditional only on the
single parameterized classical zero-free-region package. -/
theorem statement_of_primitiveZeroFreeRegion
    (hzf : Chen.PrimitiveZeroFreeRegion) : Statement := by
  intro A hA
  let a : ℕ := ⌈A⌉₊
  obtain ⟨B, hB, C, hC, hnat⟩ := bombieriVinogradov_nat hzf a
  refine ⟨(B : ℝ), C, ?_, hC, ?_⟩
  · exact_mod_cast (show 0 < B by omega)
  filter_upwards [hnat,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 1)] with x hnat hlogOne
  intro Q hQ
  let L : ℝ := Real.log (x : ℝ)
  change 1 ≤ L at hlogOne
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hQnat : (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
    simpa only [L, Real.rpow_natCast] using hQ
  have hraw := hnat Q hQnat
  have hAceil : A ≤ (a : ℝ) := by
    dsimp only [a]
    exact Nat.le_ceil A
  have hpow : L ^ A ≤ L ^ a := by
    calc
      L ^ A ≤ L ^ (a : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne hAceil
      _ = L ^ a := Real.rpow_natCast L a
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
        C * (x : ℝ) / L ^ a := by simpa only [L] using hraw
    _ ≤ C * (x : ℝ) / L ^ A :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le (by positivity))
        (Real.rpow_pos_of_pos hLpos A) hpow

/-- **Bombieri--Vinogradov.**  All algebraic, large-sieve, Vaughan,
imprimitive-character, smoothing, and contour steps are proved in the
preceding files, using the proved analytic package
`Chen.primitive_zero_free_region`. -/
theorem bombieriVinogradov : Statement :=
  statement_of_primitiveZeroFreeRegion Chen.primitive_zero_free_region

end Chen.BombieriVinogradov
