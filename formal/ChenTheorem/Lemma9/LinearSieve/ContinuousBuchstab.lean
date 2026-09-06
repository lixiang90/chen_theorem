import ChenTheorem.Lemma9.LinearSieve.ContinuousErrorIntegrals

open Set Finset MeasureTheory

namespace Chen.LinearSieve

theorem hasDerivAt_shift_upperContinuousError (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => upperContinuousError (t - 1))
      (deriv upperContinuousError (s - 1)) s := by
  have h := (hasDerivAt_upperContinuousError_all (s - 1) (by linarith)).differentiableAt.hasDerivAt
  convert! h.comp s ((hasDerivAt_id s).sub_const 1) using 1
  simp only [mul_one]

theorem hasDerivAt_shift_lowerContinuousError (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => lowerContinuousError (t - 1))
      (deriv lowerContinuousError (s - 1)) s := by
  have h := (hasDerivAt_lowerContinuousError (s - 1) (by linarith)).differentiableAt.hasDerivAt
  convert! h.comp s ((hasDerivAt_id s).sub_const 1) using 1
  simp only [mul_one]

theorem continuousOn_deriv_shift_upperContinuousError :
    ContinuousOn (deriv (fun t => upperContinuousError (t - 1))) (Ioi 2) := by
  have hc := continuousOn_deriv_upperContinuousError_all.comp
    (continuousOn_id.sub continuousOn_const)
    (show MapsTo (fun s : ℝ => s - 1) (Ioi 2) (Ioi 1) from
      fun s hs => by change 1 < s - 1; linarith [show 2 < s from hs])
  apply hc.congr
  intro s hs
  exact (hasDerivAt_shift_upperContinuousError s hs).deriv

theorem continuousOn_deriv_shift_lowerContinuousError :
    ContinuousOn (deriv (fun t => lowerContinuousError (t - 1))) (Ioi 3) := by
  have hc := continuousOn_deriv_lowerContinuousError.comp
    (continuousOn_id.sub continuousOn_const)
    (show MapsTo (fun s : ℝ => s - 1) (Ioi 3) (Ioi 2) from
      fun s hs => by change 2 < s - 1; linarith [show 3 < s from hs])
  apply hc.congr
  intro s hs
  exact (hasDerivAt_shift_lowerContinuousError s hs).deriv

/-- The continuous error functions themselves control the prime-weighted
Buchstab sums. The stated open parameter ranges keep the weights smooth;
no abstract envelope regularity or integral bound is assumed. -/
theorem weighted_buchstab_continuous_errors_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (3 < sieveParameter D z →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, lowerContinuousError (sieveParameter D p - 1) *
          buchstabCoefficient P z p) ≤ upperContinuousError (sieveParameter D z) +
            2 * K * lowerContinuousError (sieveParameter D z - 1) / Real.log w) ∧
      (2 < sieveParameter D z →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, upperContinuousError (sieveParameter D p - 1) *
          buchstabCoefficient P z p) ≤ lowerContinuousError (sieveParameter D z) +
            2 * K * upperContinuousError (sieveParameter D z - 1) / Real.log w) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz P hP hodd
  have hsw : sieveParameter D z ≤ sieveParameter D w :=
    sieveParameter_antitone hD (by change 1 < w; linarith)
      (by change 1 < (z : ℝ); linarith) hwz
  constructor
  · intro hs
    have hsub : Set.Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi 3 :=
      fun s ht => hs.trans_le ht.1
    have h := hb D w z hD hw hwz P hP hodd (fun s => lowerContinuousError (s - 1))
      (fun s ht => (hasDerivAt_shift_lowerContinuousError s (hsub ht)).differentiableAt)
      (continuousOn_deriv_shift_lowerContinuousError.mono hsub)
      (fun s ht => (lowerContinuousError_bounds (s - 1) (by
        have hst := hsub ht; change 3 < s at hst; linarith)).1)
      (fun s ht => by
        rw [(hasDerivAt_shift_lowerContinuousError s (hsub ht)).deriv]
        apply deriv_lowerContinuousError_nonpos
        have hst := hsub ht; change 3 < s at hst; linarith)
      (antitoneOn_mul_shift_lowerContinuousError.mono (fun s ht => by
        change 3 ≤ s
        exact le_of_lt (hsub ht)))
    have hi := parameter_integral_shift_lowerContinuousError_le _ _ hs hsw
    exact h.trans (_root_.add_le_add hi le_rfl)
  · intro hs
    have hsub : Set.Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi 2 :=
      fun s ht => hs.trans_le ht.1
    have h := hb D w z hD hw hwz P hP hodd (fun s => upperContinuousError (s - 1))
      (fun s ht => (hasDerivAt_shift_upperContinuousError s (hsub ht)).differentiableAt)
      (continuousOn_deriv_shift_upperContinuousError.mono hsub)
      (fun s ht => (upperContinuousError_bounds (s - 1) (by
        have hst := hsub ht; change 2 < s at hst; linarith)).1)
      (fun s ht => by
        rw [(hasDerivAt_shift_upperContinuousError s (hsub ht)).deriv]
        apply deriv_upperContinuousError_nonpos_all
        have hst := hsub ht; change 2 < s at hst; linarith)
      (antitoneOn_mul_shift_upperContinuousError.mono (fun s ht => by
        change 2 < s
        exact hsub ht))
    have hi := parameter_integral_shift_upperContinuousError_le _ _ hs hsw
    exact h.trans (_root_.add_le_add hi le_rfl)

end Chen.LinearSieve
