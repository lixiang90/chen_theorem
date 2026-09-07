import ChenTheorem.Analysis.SignedTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace Chen

theorem backwardTaylorCoeff_inv_sub_one (n : ℕ) :
    backwardTaylorCoeff (fun s : ℂ => (s - 1)⁻¹) 2 n = 1 := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_comp_sub_const]
  change (-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ *
    iteratedDeriv n (Inv.inv : ℂ → ℂ) (2 - 1) = 1
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  norm_num only [show (2 : ℂ) - 1 = 1 by norm_num, one_zpow, mul_one]
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ) ^ n * (-1) ^ n) *
        ((n.factorial : ℂ)⁻¹ * n.factorial) := by ring
    _ = 1 := by rw [hs, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), mul_one]

theorem backwardTaylorCoeff_const_mul (f : ℂ → ℂ) (c a : ℂ) (n : ℕ) :
    backwardTaylorCoeff (fun s => a * f s) c n = a * backwardTaylorCoeff f c n := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_const_mul_field]
  ring

theorem backwardTaylorCoeff_pole (a : ℂ) (n : ℕ) :
    backwardTaylorCoeff (fun s : ℂ => a / (s - 1)) 2 n = a := by
  simp only [div_eq_mul_inv]
  rw [backwardTaylorCoeff_const_mul, backwardTaylorCoeff_inv_sub_one, mul_one]

theorem backwardTaylorCoeff_sub {f g : ℂ → ℂ} {c : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f c) (hg : ContDiffAt ℂ n g c) :
    backwardTaylorCoeff (fun s => f s - g s) c n =
      backwardTaylorCoeff f c n - backwardTaylorCoeff g c n := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_fun_sub hf hg]
  ring

end Chen
