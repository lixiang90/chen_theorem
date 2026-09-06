import ChenTheorem.Lemma6.DirichletEulerLogDerivative
import ChenTheorem.Lemma6.LFunctionZeroPoleRealPart

open Set Filter
open scoped Topology

namespace Chen

theorem logDeriv_LFunction_changeLevel {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (s : ℂ) (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction (χ.changeLevel hdq)) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
      logDeriv (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have he : DirichletCharacter.LFunction (χ.changeLevel hdq) =ᶠ[𝓝 s]
      (fun z => DirichletCharacter.LFunction χ z *
        ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) := by
    filter_upwards [isOpen_ne.mem_nhds hsne] with z hz
    exact DirichletCharacter.LFunction_changeLevel hdq χ (Or.inr hz)
  have hpne : (∏ p ∈ q.primeFactors, dirichletEulerFactor χ p s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact dirichletEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp).two_le s hs.le
  have hpd : DifferentiableAt ℂ
      (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
    exact DifferentiableAt.fun_finsetProd (fun p hp =>
      (hasDerivAt_dirichletEulerFactor χ (Nat.pos_of_mem_primeFactors hp).ne' s).differentiableAt)
  calc
    _ = logDeriv (fun z => DirichletCharacter.LFunction χ z *
        ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s := by
      simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    _ = _ := logDeriv_mul s
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hsne) hs.le) hpne
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hsne)) hpd

theorem norm_logDeriv_LFunction_changeLevel_sub_le {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (χ.changeLevel hdq)) s -
      logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ Real.log q := by
  rw [logDeriv_LFunction_changeLevel hdq χ s hs, add_sub_cancel_left]
  exact norm_logDeriv_dirichletEulerProduct_le χ q (Nat.pos_of_ne_zero (NeZero.ne q)) s hs.le

end Chen
