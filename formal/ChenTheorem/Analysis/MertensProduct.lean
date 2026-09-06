import ChenTheorem.Analysis.PNT.IEANTN.Mertens

open Filter Finset
open scoped Classical

namespace Chen

/-- Euler's prime product at a natural cutoff. -/
noncomputable def primeEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ y.primesLE, (1 - (1 : ℝ) / p)

theorem primeEulerProduct_eq_Ioc (y : ℕ) :
    primeEulerProduct y = ∏ p ∈ Ioc 0 y with p.Prime, (1 - (1 : ℝ) / p) := by
  apply prod_congr
  · ext p
    simp only [Nat.mem_primesLE, mem_filter, mem_Ioc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  · intro p _; rfl

/-- Mertens' third theorem with its exact exponential remainder, obtained
from the locally included proof. -/
theorem primeEulerProduct_eq (y : ℕ) (hy : 1 < y) :
    primeEulerProduct y = Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ y) / Real.log y := by
  rw [primeEulerProduct_eq_Ioc]
  simpa only [Nat.floor_natCast] using
    Mertens.prod_one_minus_div_prime_eq (x := (y : ℝ)) (by exact_mod_cast hy)

/-- The normalization used in the one-dimensional sieve product. -/
theorem primeEulerProduct_mul_log_tendsto :
    Tendsto (fun y : ℕ => primeEulerProduct y * Real.log y) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hlim := (tendsto_const_nhds (x := Real.exp (-Real.eulerMascheroniConstant))).mul
    ((hE.comp tendsto_natCast_atTop_atTop).rexp)
  simp only [Real.exp_zero, mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with y hy
  have hlog : Real.log (y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  rw [primeEulerProduct_eq y (by omega), div_mul_cancel₀ _ hlog]
  rfl

end Chen
