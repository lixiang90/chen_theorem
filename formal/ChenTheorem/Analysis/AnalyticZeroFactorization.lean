import ChenTheorem.Analysis.DiskBlaschkeProduct

open Set Metric Filter Topology MeromorphicOn

namespace Chen

/-- Continuity removes the exceptional discrete set from an identity on an open set. -/
theorem eqOn_of_continuousOn_codiscrete {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : f =ᶠ[codiscreteWithin U] g) : EqOn f g U := by
  intro z hz
  have hpunct : f =ᶠ[𝓝[≠] z] g := by
    have he' := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he z hz
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
      eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hz)
    filter_upwards [he', hmem] with w hw hwU
    exact hw.resolve_right (by simpa using hwU)
  have hnhds := ((hf.continuousAt (hU.mem_nhds hz)).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hg.continuousAt (hU.mem_nhds hz))).mp hpunct
  exact hnhds.eq_of_nhds

theorem analyticOnNhd_of_canonicalDecomp {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : Complex.CanonicalDecomp f g R) : AnalyticOnNhd ℂ g (closedBall 0 R) := by
  apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
  intro z
  change 0 ≤ divisor g (closedBall 0 R) z
  rw [D.divisor_eq_divisor hR]
  exact (hf.mono sphere_subset_closedBall).divisor_nonneg z

/-- The analytic Blaschke factorization is an exact identity even at zeros
and on the boundary, not merely a codiscrete identity. -/
theorem canonicalDecomp_eqOn_closedBall {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : Complex.CanonicalDecomp f g R) :
    EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) := by
  have hg := analyticOnNhd_of_canonicalDecomp hR hf D
  have hp := analyticOnNhd_diskBlaschkeProduct f R
  have he := D.eventuallyEq
  rw [canonical_product_eq_diskBlaschkeProduct hf] at he
  change f =ᶠ[codiscreteWithin (closedBall 0 R)] (fun z => diskBlaschkeProduct f R z * g z) at he
  have hb := eqOn_of_continuousOn_codiscrete isOpen_ball
    (hf.continuousOn.mono ball_subset_closedBall)
    ((hp.mul hg).continuousOn.mono ball_subset_closedBall)
    (he.filter_mono (codiscreteWithin_mono ball_subset_closedBall))
  apply hb.of_subset_closure hf.continuousOn (hp.mul hg).continuousOn ball_subset_closedBall
  rw [closure_ball _ hR.ne']

/-- A nonzero center value gives an analytic zero-free factor on the disk;
all interior zeros and their multiplicities occur in the explicit finite product. -/
theorem exists_analytic_blaschke_factorization {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) := by
  have hmem : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have horder : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 hmem).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  have horders : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hmem u.property horder
  obtain ⟨g, D⟩ := hf.meromorphicOn.exists_canonicalDecomp horders
  exact ⟨g, analyticOnNhd_of_canonicalDecomp hR hf D, D.ne_zero,
    canonicalDecomp_eqOn_closedBall hR hf D⟩

end Chen
