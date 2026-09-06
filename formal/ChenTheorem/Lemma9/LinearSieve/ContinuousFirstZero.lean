import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

open Set

namespace Chen.LinearSieve

theorem exists_first_zero_of_nonneg (g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn g (Icc a b)) (ha : g a < 0) (hb : 0 ≤ g b) :
    ∃ m ∈ Ioc a b, g m = 0 ∧ ∀ t ∈ Ico a m, g t < 0 := by
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc hab hc ⟨ha.le, hb⟩
  let K := Icc a b ∩ g ⁻¹' {0}
  have hKc : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
    (fun _ h => h.1)
  have hKn : K.Nonempty := ⟨z, hz, hgz⟩
  obtain ⟨m, hm, hmin⟩ := hKc.exists_isMinOn hKn (continuousOn_id (s := K))
  have hgm : g m = 0 := hm.2
  have ham : a < m := by
    have := hm.1.1
    by_contra hn
    have he : m = a := le_antisymm (le_of_not_gt hn) this
    rw [he] at hgm
    linarith
  refine ⟨m, ⟨ham, hm.1.2⟩, hgm, ?_⟩
  intro t ht
  by_contra hn
  have hc' := hc.mono (show Icc a t ⊆ Icc a b from
    fun x hx => ⟨hx.1, hx.2.trans (ht.2.le.trans hm.1.2)⟩)
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc ht.1 hc' ⟨ha.le, le_of_not_gt hn⟩
  have hzK : z ∈ K := ⟨⟨hz.1, hz.2.trans (ht.2.le.trans hm.1.2)⟩, hgz⟩
  have hmz : m ≤ z := hmin hzK
  linarith [hz.2, ht.2]

end Chen.LinearSieve
