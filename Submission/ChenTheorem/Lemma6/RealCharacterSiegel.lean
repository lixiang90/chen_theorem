import Submission.ChenTheorem.Lemma6.RealZeroRepulsion
import Submission.ChenTheorem.Lemma6.RealCharacterChangeLevelZeros

set_option autoImplicit true
namespace Chen

/-- Siegel's ineffective real zero-free region. The choice of a fixed possible
exceptional character accounts for the non-effective constant. -/
theorem exists_real_character_siegel_region {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ ≠ 1 → χ ^ 2 = 1 → ∀ β : ℝ,
      1 - c * (q : ℝ) ^ (-ε) < β → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  classical
  let δ : ℝ := min (1 / 16) (ε / 144)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 16 := min_le_left _ _
  have hδ₂ : δ ≤ ε / 144 := min_le_right _ _
  by_cases H : ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q ∧ χ ≠ 1 ∧ χ ^ 2 = 1 ∧ ∃ β : ℝ,
        1 - δ < β ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0
  · obtain ⟨q₁, inst₁, χ₁, hq₁, hχ₁, hsq₁, β₁, hβ₁, hz₁⟩ := H
    letI : NeZero q₁ := inst₁
    have hq₁R : (1 : ℝ) ≤ q₁ := by exact_mod_cast (by omega : 1 ≤ q₁)
    have hq₁pos : (0 : ℝ) < q₁ := by linarith
    have hβ₁' : β₁ < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₁ (Or.inl hχ₁)
        (by simpa using le_of_not_gt hn) hz₁
    have hβ₁lower : 7 / 8 < β₁ := by linarith
    obtain ⟨r, A, hr, hA, hrep⟩ := exists_real_zero_repulsion_bound (by positivity : 0 < ε / 12)
    obtain ⟨η, hη, hnonzero⟩ := exists_nonprincipal_one_nonvanishing_ball χ₁ hχ₁
    let c₀ : ℝ := (1 - β₁) / (A * (q₁ : ℝ) ^ ε)
    have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
    let c : ℝ := min (min r η) (min (1 / 2) c₀)
    have hc : 0 < c := lt_min (lt_min hr hη) (lt_min (by norm_num) hc₀)
    have hcr : c ≤ r := (min_le_left _ _).trans (min_le_left _ _)
    have hcη : c ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have hchalf : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hcc₀ : c ≤ c₀ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨c, hc, ?_⟩
    intro q₂ inst₂ χ₂ hq₂ hχ₂ hsq₂ β₂ hβ₂ hz₂
    have hq₂R : (1 : ℝ) ≤ q₂ := by exact_mod_cast (by omega : 1 ≤ q₂)
    have hq₂pos : (0 : ℝ) < q₂ := by linarith
    have hpow : (q₂ : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq₂R (by linarith)
    have hgap : 1 - β₂ < c := by
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    have hβ₂' : β₂ < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₂ (Or.inl hχ₂)
        (by simpa using le_of_not_gt hn) hz₂
    have hβ₂pos : 0 < β₂ := by linarith
    let Q : ℕ := q₁ * q₂
    have hQ : 2 ≤ Q := by dsimp [Q]; nlinarith
    letI : NeZero Q := ⟨by omega⟩
    have hd₁ : q₁ ∣ Q := Nat.dvd_mul_right _ _
    have hd₂ : q₂ ∣ Q := Nat.dvd_mul_left _ _
    let χ := χ₁.changeLevel hd₁
    let ψ := χ₂.changeLevel hd₂
    have hχ : χ ≠ 1 := hχ₁ ∘ (DirichletCharacter.changeLevel_eq_one_iff hd₁).mp
    have hψ : ψ ≠ 1 := hχ₂ ∘ (DirichletCharacter.changeLevel_eq_one_iff hd₂).mp
    have hχsq : χ ^ 2 = 1 := real_character_changeLevel hd₁ χ₁ hsq₁
    have hψsq : ψ ^ 2 = 1 := real_character_changeLevel hd₂ χ₂ hsq₂
    have hzχ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 :=
      (LFunction_changeLevel_zero_iff hd₁ χ₁ hχ₁ _ (by simpa using (show 0 < β₁ by linarith))).mpr hz₁
    have hzψ : DirichletCharacter.LFunction ψ (β₂ : ℂ) = 0 :=
      (LFunction_changeLevel_zero_iff hd₂ χ₂ hχ₂ _ hβ₂pos).mpr hz₂
    by_cases hprod : χ * ψ = 1
    · have heq : ψ = χ := real_character_eq_of_mul_eq_one χ ψ hχsq hprod
      rw [heq] at hzψ
      have hz := (LFunction_changeLevel_zero_iff hd₁ χ₁ hχ₁ _ hβ₂pos).mp hzψ
      apply hnonzero (β₂ : ℂ) _ hz
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith : β₂ - 1 < 0)]
      linarith
    · have hbound := hrep Q χ ψ hQ hχ hψ hprod hχsq hψsq β₁ β₂
        hβ₁lower hβ₁' hzχ (by linarith) hβ₂'.le hzψ
      have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
      have hQpos : (0 : ℝ) < Q := by linarith
      have hexp : 36 * (1 - β₁) + 3 * (ε / 12) ≤ ε := by linarith
      have hQpow := Real.rpow_le_rpow_of_exponent_le hQR hexp
      have hlower : (1 - β₁) / (A * (Q : ℝ) ^ ε) ≤ 1 - β₂ := by
        apply le_trans _ hbound
        exact div_le_div_of_nonneg_left (by linarith) (by positivity)
          (mul_le_mul_of_nonneg_left hQpow hA.le)
      have hid : c₀ * (q₂ : ℝ) ^ (-ε) = (1 - β₁) / (A * (Q : ℝ) ^ ε) := by
        dsimp [c₀, Q]
        rw [Nat.cast_mul, Real.mul_rpow hq₁pos.le hq₂pos.le, Real.rpow_neg hq₂pos.le]
        ring
      rw [← hid] at hlower
      have := mul_le_mul_of_nonneg_right hcc₀ (Real.rpow_nonneg hq₂pos.le (-ε))
      linarith
  · refine ⟨δ, hδ, ?_⟩
    intro q inst χ hq hχ hsq β hβ hz
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hqR (by linarith : -ε ≤ 0)
    have hmul := mul_le_mul_of_nonneg_left hpow hδ.le
    exact H ⟨q, inst, χ, hq, hχ, hsq, β, by linarith, hz⟩

end Chen
