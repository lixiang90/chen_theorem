import Submission.ChenTheorem.Lemma6.RealZeroUniquenessTools
import Submission.ChenTheorem.Lemma6.RealZeroBox

set_option autoImplicit true
namespace Chen

theorem exists_primitive_real_zero_unique :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β₁ β₂ : ℝ,
      1 - c / Real.log ((q : ℝ) * 2) < β₁ →
      1 - c / Real.log ((q : ℝ) * 2) < β₂ →
      DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 →
      DirichletCharacter.LFunction χ (β₂ : ℂ) = 0 → β₁ = β₂ := by
  obtain ⟨δ, C, hδ, hC, hu⟩ := exists_real_character_logDeriv_real_axis_bound
  let B : ℝ := 2 * C + 60001
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := min (δ / 4) (min (1 / 8) (1 / (4 * B)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a * B ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
      (show a ≤ 1 / (4 * B) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q inst χ hq hχ hsq β₁ β₂ hβ₁ hβ₂ hf₁ hf₂
  by_contra hne
  let L : ℝ := Real.log ((q : ℝ) * 2)
  have hL : 3 / 4 ≤ L := by simpa [L] using conductor_height_log_ge_threeQuarters q hq 0
  have hLp : 0 < L := by linarith
  let x : ℝ := a / L
  let σ : ℝ := 1 + x
  let y₁ : ℝ := σ - β₁
  let y₂ : ℝ := σ - β₂
  let D : ℝ := C + Real.log q / 4 + 60000 * L
  have hx : 0 < x := div_pos ha hLp
  have hxL : x * L = a := div_mul_cancel₀ _ hLp.ne'
  have hxδ : x < δ := by apply (div_lt_iff₀ hLp).mpr; nlinarith
  have hx6 : x ≤ 1 / 6 := by apply (div_le_iff₀ hLp).mpr; linarith
  have hquot : (a / 8) / L = x / 8 := by dsimp [x]; ring
  change 1 - (a / 8) / L < β₁ at hβ₁
  change 1 - (a / 8) / L < β₂ at hβ₂
  rw [hquot] at hβ₁ hβ₂
  have hzero_le : ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 := by
    intro β hb
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hb
  have hb₁ := hzero_le β₁ hf₁
  have hb₂ := hzero_le β₂ hf₂
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ' : σ ≤ 3 / 2 := by dsimp [σ]; linarith
  have hσδ : σ < 1 + δ := by dsimp [σ]; linarith
  have hpair := primitive_LFunction_logDeriv_re_ge_two_real_zeros hq hχ σ β₁ β₂
    hσ hσ' (by linarith) (by linarith) hne hf₁ hf₂
  have hup := hu q χ hsq σ hσ hσδ
  have hlogq : Real.log q ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hD : D ≤ B * L := by dsimp [D, B]; nlinarith
  have hDx : D * x ≤ 1 / 4 := by
    calc
      _ ≤ (B * L) * x := mul_le_mul_of_nonneg_right hD hx.le
      _ = B * a := by rw [mul_assoc, mul_comm L x, hxL]
      _ ≤ _ := by nlinarith [haB]
  have hy₁ : 0 < y₁ := by dsimp [y₁, σ]; linarith
  have hy₂ : 0 < y₂ := by dsimp [y₂, σ]; linarith
  have h₁ : y₁ ≤ 9 * x / 8 := by dsimp [y₁, σ]; linarith
  have h₂ : y₂ ≤ 9 * x / 8 := by dsimp [y₂, σ]; linarith
  have hi : 1 / y₁ + 1 / y₂ ≤ 1 / x + D := by
    have he : σ - 1 = x := by dsimp [σ]; ring
    rw [he] at hup
    change 1 / y₁ + 1 / y₂ - 60000 * L ≤ _ at hpair
    dsimp [D]
    linarith
  exact two_real_zero_gaps_contradiction hx hy₁ hy₂ h₁ h₂ hDx hi

theorem exists_primitive_real_zero_box_subsingleton :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
      Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * 2) < s.re ∧
        |s.im| ≤ c / Real.log ((q : ℝ) * 2) ∧ DirichletCharacter.LFunction χ s = 0} := by
  obtain ⟨cR, hcR, hreal⟩ := exists_primitive_real_zero_box_im_eq_zero
  obtain ⟨cU, hcU, huniq⟩ := exists_primitive_real_zero_unique
  refine ⟨min cR cU, lt_min hcR hcU, ?_⟩
  intro q inst χ hq hχ hsq s hs t ht
  have hL : 0 < Real.log ((q : ℝ) * 2) := by
    have h := conductor_height_log_ge_threeQuarters q hq 0
    simp only [abs_zero, zero_add] at h
    linarith
  have hR := div_le_div_of_nonneg_right (min_le_left cR cU) hL.le
  have hU := div_le_div_of_nonneg_right (min_le_right cR cU) hL.le
  have hsi : s.im = 0 := hreal q χ hq hχ hsq s (by linarith [hs.1])
    (hs.2.1.trans hR) hs.2.2
  have hti : t.im = 0 := hreal q χ hq hχ hsq t (by linarith [ht.1])
    (ht.2.1.trans hR) ht.2.2
  have hsreal : (s.re : ℂ) = s := by apply Complex.ext <;> simp [hsi]
  have htreal : (t.re : ℂ) = t := by apply Complex.ext <;> simp [hti]
  have he := huniq q χ hq hχ hsq s.re t.re (by linarith [hs.1]) (by linarith [ht.1])
    (by rw [hsreal]; exact hs.2.2) (by rw [htreal]; exact ht.2.2)
  apply Complex.ext
  · exact he
  · rw [hsi, hti]

end Chen
