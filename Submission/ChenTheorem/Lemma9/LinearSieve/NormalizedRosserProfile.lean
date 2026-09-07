import Submission.ChenTheorem.Lemma9.LinearSieve.WeightedRosserSum

set_option autoImplicit true
open Set Filter
open scoped Topology Classical

namespace Chen.LinearSieve

noncomputable def powerRosserMainTerm (a : ℝ) (P S : Finset ℕ) (x : ℕ) : ℝ :=
  (x : ℝ) * rosserEval P primeDensity (powerSieveCutoff (1 / 10) x + 1) false
      (powerSieveCutoff a x) / Real.log x -
    (1 / 2) * ((∑ p ∈ S, ((x : ℝ) / Nat.totient p) *
      rosserEval P primeDensity (powerSieveCutoff (1 / 10) x + 1) true
        (powerSieveCutoff a x / p : ℕ)) / Real.log (countCutoff x))

theorem exists_sieve_profile_error (a K : ℝ) (hK : K < chenContinuousSieveProfile a) :
    ∃ ε : ℝ, 0 < ε ∧ K <
      20 * Real.exp (-Real.eulerMascheroniConstant) * (lowerLinearSieveFunction (10 * a) - ε) -
      10 * Real.exp (-Real.eulerMascheroniConstant) * (1 + ε) *
        (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α) := by
  let G : ℝ → ℝ := fun ε =>
    20 * Real.exp (-Real.eulerMascheroniConstant) * (lowerLinearSieveFunction (10 * a) - ε) -
      10 * Real.exp (-Real.eulerMascheroniConstant) * (1 + ε) *
        (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α)
  have hc : ContinuousAt G 0 := by unfold G; fun_prop
  have hzero : G 0 = chenContinuousSieveProfile a := by simp [G, chenContinuousSieveProfile]
  have he := hc.tendsto.eventually (Ioi_mem_nhds (show K < G 0 by rwa [hzero]))
  have hh : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ K < G ε := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds he, self_mem_nhdsWithin] with ε hε hpos
    exact ⟨hpos, hε⟩
  exact hh.exists

/-- The Rosser main term attains every constant strictly below Chen's
continuous profile, for either family of local residue exclusions. -/
theorem eventually_powerRosserMainTerm_lower
    (P S : ℕ → Finset ℕ) (C : ℕ → ℝ)
    (hP : ∀ x, 2 ≤ x → ∀ p ∈ P x, p.Prime)
    (hodd : ∀ x, 2 ≤ x → ∀ p ∈ P x, 2 < p)
    (hS : ∀ x, S x ⊆ midPrimes x)
    (hC : ∀ x, 0 < C x)
    (hnorm : Tendsto (fun x : ℕ => sieveProduct (P x) primeDensity
      (powerSieveCutoff (1 / 10) x + 1) * Real.log x / C x) atTop
      (𝓝 (20 * Real.exp (-Real.eulerMascheroniConstant))))
    (a K : ℝ) (ha : 29 / 60 < a) (ha' : a < 1 / 2)
    (hK : K < chenContinuousSieveProfile a) :
    ∀ᶠ x : ℕ in atTop,
      K * ((x : ℝ) * C x / Real.log x ^ 2) ≤ powerRosserMainTerm a (P x) (S x) x := by
  obtain ⟨ε, hε, hεK⟩ := exists_sieve_profile_error a K hK
  let V : ℕ → ℝ := fun x => sieveProduct (P x) primeDensity (powerSieveCutoff (1 / 10) x + 1)
  let H : ℕ → ℝ := fun x => (V x * Real.log x / C x) *
    ((lowerLinearSieveFunction (10 * a) - ε) -
      (1 / 2) * (1 + ε) * upperSieveMidPrimeSum a x * (Real.log x / Real.log (countCutoff x)))
  have hlim : Tendsto H atTop (𝓝
      (20 * Real.exp (-Real.eulerMascheroniConstant) * (lowerLinearSieveFunction (10 * a) - ε) -
      10 * Real.exp (-Real.eulerMascheroniConstant) * (1 + ε) *
        (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α))) := by
    have ht := hnorm.mul ((tendsto_const_nhds (x := lowerLinearSieveFunction (10 * a) - ε)).sub
      (((tendsto_upperSieveMidPrimeSum a ha).const_mul ((1 / 2) * (1 + ε))).mul
        log_div_log_countCutoff_tendsto))
    convert ht using 1
    congr 1
    ring
  filter_upwards [hlim.eventually (Ioi_mem_nhds hεK),
    eventually_rosser_lower_parent_power a ε ha ha' hε,
    eventually_weighted_rosser_child_sum a ε ha ha' hε,
    eventually_log_countCutoff (1 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with x hHK hlower hupper hcut hx
  have hL := Real.log_pos (show (1 : ℝ) < x by exact_mod_cast (show 1 < x by omega))
  have hT := Real.log_pos hcut.1
  have hscale : 0 ≤ (x : ℝ) * C x / Real.log x ^ 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg x) (hC x).le) (sq_nonneg _)
  have hlo := hlower (P x) (hP x hx) (hodd x hx)
  have hup := hupper (P x) (hP x hx) (hodd x hx) (S x) (hS x)
  calc
    _ ≤ H x * ((x : ℝ) * C x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right hHK.le hscale
    _ = (x : ℝ) * (V x * (lowerLinearSieveFunction (10 * a) - ε)) / Real.log x -
        (1 / 2) * (((x : ℝ) * V x * (1 + ε) * upperSieveMidPrimeSum a x) /
          Real.log (countCutoff x)) := by
      dsimp [H]
      field_simp [hL.ne', hT.ne', (hC x).ne']
    _ ≤ _ := by
      unfold powerRosserMainTerm
      apply sub_le_sub
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg x)) hL.le
      · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hup hT.le) (by norm_num)

end Chen.LinearSieve
