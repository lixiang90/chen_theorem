import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.RemovableSingularity

open scoped Topology

namespace Chen

/-- The entire extension of `(s - 1) * ζ(s)`, using mathlib's pole removal. -/
noncomputable abbrev zetaPoleFactor : ℂ → ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1

theorem zetaPoleFactor_one : zetaPoleFactor 1 = 1 := by
  simp [zetaPoleFactor, DirichletCharacter.LFunctionTrivChar₁]

theorem zetaPoleFactor_eq {s : ℂ} (hs : s ≠ 1) :
    zetaPoleFactor s = (s - 1) * riemannZeta s := by
  rw [zetaPoleFactor, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  simp

theorem differentiable_zetaPoleFactor : Differentiable ℂ zetaPoleFactor :=
  DirichletCharacter.differentiable_LFunctionTrivChar₁ 1

/-- The regular part of `ζ(s) * g(s)` after subtracting its residue at one.
The value at one is given by the derivative of the numerator. -/
noncomputable def regularizedZetaMul (g : ℂ → ℂ) : ℂ → ℂ :=
  dslope (fun s => zetaPoleFactor s * g s) 1

theorem differentiable_regularizedZetaMul {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (regularizedZetaMul g) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (c := (1 : ℂ)) Filter.univ_mem).mpr
    (differentiable_zetaPoleFactor.mul hg).differentiableOn

theorem regularizedZetaMul_eq {g : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) :
    regularizedZetaMul g s = riemannZeta s * g s - g 1 / (s - 1) := by
  rw [regularizedZetaMul, dslope_of_ne _ hs]
  simp only [slope, vsub_eq_sub, smul_eq_mul, zetaPoleFactor_one, one_mul, zetaPoleFactor_eq hs]
  field_simp

end Chen
