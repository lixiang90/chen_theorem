import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabRight
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit true

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

theorem right_derivative_nonneg_of_monotoneOn (w z t : ℝ) (f : ℝ → ℝ) (g : ℝ)
    (ht : t ∈ Ioo w z) (hm : MonotoneOn f (Icc w z))
    (hd : HasDerivWithinAt f g (Ioi t) t) : 0 ≤ g := by
  have ha : AccPt t (𝓟 (Ioc t z)) := by
    rw [accPt_principal_iff_nhdsWithin]
    have he : Ioc t z \ {t} = Ioc t z := by
      ext x
      simp only [Set.mem_sdiff, mem_Ioc, mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, ne_of_gt h.1⟩
    rw [he]
    exact left_nhdsWithin_Ioc_neBot ht.2
  exact (hd.mono (fun _ hx => hx.1)).nonneg_of_monotoneOn ha
    (hm.mono (fun x hx => ⟨ht.1.le.trans hx.1.le, hx.2⟩))

/-- Monotonicity of the weight supplies the derivative sign. Taking the
positive part handles arbitrary derivative values at the two endpoints. -/
theorem weighted_buchstab_partial_summation_monotone_right :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ f g : ℝ → ℝ, ContinuousOn f (Icc w (z : ℝ)) →
        (∀ t ∈ Ioo w (z : ℝ), HasDerivWithinAt f (g t) (Ioi t) t) →
        IntegrableOn g (Icc w (z : ℝ)) →
        (∀ t ∈ Icc w (z : ℝ), 0 ≤ f t) → MonotoneOn f (Icc w (z : ℝ)) →
        (∀ t ∈ Icc w (z : ℝ), f t * Real.log z ≤ f z * Real.log t) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) ≤
          Real.log z * (∫ t in Ioc w (z : ℝ), f t * logSieveKernel t) +
            2 * K * f z / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_partial_summation_of_hasDeriv_right
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd f g hfc hfd hgi hfn hfm hscale
  apply hb w z hw hwz P hP hodd f (fun t => max (g t) 0) hfc
  · intro t ht
    rw [max_eq_left (right_derivative_nonneg_of_monotoneOn w z t f (g t) ht hfm (hfd t ht))]
    exact hfd t ht
  · exact hgi.pos_part
  · exact hfn
  · exact fun t _ => le_max_right _ _
  · exact hscale

end Chen.LinearSieve
