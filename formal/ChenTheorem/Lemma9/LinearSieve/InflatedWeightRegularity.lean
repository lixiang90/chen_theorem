import ChenTheorem.Lemma9.LinearSieve.ChildInflationDerivative
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryWeightDerivative

open Set MeasureTheory

namespace Chen.LinearSieve

theorem continuousOn_inflatedChildAuxiliaryWeight (d δ D a b c : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (ha : 0 ≤ a) (hb : a + 1 < b) (hH : ContinuousOn H (Ioi a)) :
    ContinuousOn (fun t => inflatedChildAuxiliaryWeight d δ D t H) (Icc b c) := by
  have hp : ∀ t ∈ Icc b c, 1 < t := by intro t ht; linarith [ht.1]
  have hi := (continuousOn_auxiliaryChildInflation d D hD).mono
    (show Icc b c ⊆ Ioi 0 from fun t ht => by change 0 < t; linarith [hp t ht])
  have hw := (continuousOn_childAuxiliaryWeight δ).mono hp
  have hh := hH.comp (continuousOn_id.sub continuousOn_const)
    (show MapsTo (fun t : ℝ => t - 1) (Icc b c) (Ioi a) from
      fun t ht => by change a < t - 1; linarith [ht.1])
  exact (hi.mul hw).mul hh

noncomputable def inflatedAuxiliaryPrimeSlope (d δ : ℝ) (H S : ℝ → ℝ) (D t : ℝ) : ℝ :=
  childInflationPrimeSlope d D t *
    (childAuxiliaryWeight δ (sieveParameter D t) * H (sieveParameter D t - 1)) +
  auxiliaryChildInflation d D (sieveParameter D t) * auxiliaryPrimeSlope δ H S D t

theorem hasDerivWithinAt_inflatedAuxiliaryPrimeWeight_right
    (d δ D t : ℝ) (H S : ℝ → ℝ) (hD : 1 < D) (ht : 1 < t)
    (hs : 1 < sieveParameter D t)
    (hH : HasDerivWithinAt H
      (-(S (sieveParameter D t - 1) + 2 * H (sieveParameter D t - 1)) /
        (sieveParameter D t - 1)) (Iio (sieveParameter D t - 1)) (sieveParameter D t - 1)) :
    HasDerivWithinAt (fun t => inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) H)
      (inflatedAuxiliaryPrimeSlope d δ H S D t) (Ioi t) t := by
  have hi := (hasDerivAt_childInflationPrimeWeight d D t hD ht).hasDerivWithinAt (s := Ioi t)
  have hh := hasDerivWithinAt_auxiliaryPrimeWeight_right δ D t H S hD ht hs hH
  have hd := hi.mul hh
  convert! hd using 1
  · funext x
    dsimp [inflatedChildAuxiliaryWeight]
    ring

theorem integrableOn_inflatedAuxiliaryPrimeSlope (d δ D w z a : ℝ) (H S : ℝ → ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (ha : 0 ≤ a) (hs : a + 1 < sieveParameter D z)
    (hH : ContinuousOn H (Ioi a))
    (hS : IntegrableOn (fun t => S (sieveParameter D t - 1)) (Icc w z)) :
    IntegrableOn (inflatedAuxiliaryPrimeSlope d δ H S D) (Icc w z) := by
  have hu := continuousOn_sieveParameter D w z hw
  have hpos : ∀ t ∈ Icc w z, a + 1 < sieveParameter D t :=
    fun t ht => hs.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have huc : ∀ t ∈ Icc w z, 1 < sieveParameter D t := by
    intro t ht
    linarith [hpos t ht]
  have hi := (continuousOn_auxiliaryChildInflation d D hD).comp hu
    (fun t ht => sieveParameter_pos hD (by linarith [ht.1]))
  have hweight := (continuousOn_childAuxiliaryWeight δ).comp hu huc
  have hshift := hH.comp (hu.sub continuousOn_const)
    (fun t ht => by change a < sieveParameter D t - 1; linarith [hpos t ht])
  have hfirst := ((continuousOn_childInflationPrimeSlope d D w z hD hw).mul
    (hweight.mul hshift)).integrableOn_Icc (μ := volume)
  have hsecond := (integrableOn_auxiliaryPrimeSlope δ D w z a H S hD hw ha hs hH hS).mul_continuousOn hi isCompact_Icc
  apply (hfirst.add hsecond).congr_fun _ measurableSet_Icc
  intro t _
  dsimp [inflatedAuxiliaryPrimeSlope]
  ring

end Chen.LinearSieve
