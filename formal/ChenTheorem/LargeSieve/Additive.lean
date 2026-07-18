/-
The additive large sieve (inequality (4) of Chen's paper):

  `∑_{q ≤ X} ∑_{1 ≤ b ≤ q, (b,q) = 1} |S(b/q)|² ≤ (X² + πN) ∑ |aₙ|²`

for `S(α) = ∑_{n=M+1}^{M+N} aₙ e(nα)`, together with its trigonometric
Parseval inputs. The proof follows the paper: Gallagher's centered inequality
(`LargeSieve/Gallagher.lean`) applied to arcs of radius `δ/2 = 1/(2X²)` about
the Farey points, whose sum of integrals is bounded by one full period using
disjointness (after lifting the arcs into a common window `(ρ, ρ+1)` chosen in
the gap between the largest and smallest point), and the AM–GM bound
`2‖T‖‖T'‖ ≤ λ‖T‖² + λ⁻¹‖T'‖` with `λ = πN` on the cross term.

The coefficient shift `n ↦ n - (M + ⌈N/2⌉)` centers the frequencies in
`[-N/2, N/2]`, giving `∫₀¹ |T'|² ≤ π²N² ∑|aₙ|²`.
-/
import ChenTheorem.LargeSieve.Gallagher
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.CompletePartialOrder

open Set MeasureTheory intervalIntegral Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace Chen.LargeSieve

/-! ### The exponential `α ↦ exp (2πiα)` -/

/-- The complex exponential `e(α) = exp (2πiα)`. -/
noncomputable def fexp (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

@[simp] lemma fexp_zero : fexp 0 = 1 := by simp [fexp]

lemma fexp_add (α β : ℝ) : fexp (α + β) = fexp α * fexp β := by
  simp only [fexp]
  push_cast
  rw [mul_add, Complex.exp_add]

@[simp] lemma fexp_norm (α : ℝ) : ‖fexp α‖ = 1 := by
  rw [fexp, show 2 * Real.pi * Complex.I * α = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma fexp_one_eq_one : fexp 1 = 1 := by
  rw [fexp, show 2 * Real.pi * Complex.I * (1 : ℝ) = 2 * Real.pi * Complex.I by simp]
  exact Complex.exp_eq_one_iff.mpr ⟨1, by simp⟩

lemma fexp_periodic : Function.Periodic fexp 1 := fun α => by
  rw [fexp_add, fexp_one_eq_one, mul_one]

lemma fexp_int_one (k : ℤ) : fexp k = 1 := by
  rw [fexp]
  exact Complex.exp_eq_one_iff.mpr ⟨k, by push_cast; ring⟩

lemma star_fexp (β : ℝ) : star (fexp β) = fexp (-β) := by
  have h1 : fexp β * fexp (-β) = 1 := by rw [← fexp_add, add_neg_cancel, fexp_zero]
  have h2 : fexp β * star (fexp β) = 1 := by
    rw [show star (fexp β) = conj (fexp β) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, fexp_norm, one_pow, Complex.ofReal_one]
  rw [← inv_eq_of_mul_eq_one_right h1, ← inv_eq_of_mul_eq_one_right h2]

lemma fexp_periodic_mul (k : ℤ) : Function.Periodic (fun α => fexp (k * α)) 1 := by
  intro α
  show fexp ((k : ℝ) * (α + 1)) = fexp ((k : ℝ) * α)
  have h : (k : ℝ) * (α + 1) = k * α + k := by ring
  rw [h, fexp_add, fexp_int_one, mul_one]

lemma fexp_mul_continuous (c : ℝ) : Continuous fun α => fexp (c * α) := by
  have h : Continuous fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α) := by fun_prop
  have h2 := h.cexp
  rw [show (fun α : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((c : ℂ) * α))) =
      (fun α => fexp (c * α)) from ?_] at h2
  · exact h2
  · funext α
    rw [fexp]
    push_cast
    ring_nf

lemma hasDerivAt_fexp (c : ℝ) (α : ℝ) :
    HasDerivAt (fun α => fexp (c * α)) (fexp (c * α) * (2 * Real.pi * Complex.I * c)) α := by
  have h1 : HasDerivAt (fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α))
      (2 * Real.pi * Complex.I * c) α := by
    have h2 : (fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α)) =
        fun α : ℝ => (2 * Real.pi * Complex.I * c) * α := by
      funext β
      ring_nf
    rw [h2]
    have hbase : HasDerivAt (fun α : ℝ => ((α : ℝ) : ℂ)) (1 : ℂ) α := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) α
      exact Complex.ofRealCLM.hasDerivAt
    simpa using hbase.const_mul (2 * Real.pi * Complex.I * c)
  have h3 := h1.cexp
  convert h3 using 1
  · funext β
    rw [fexp]
    push_cast
    ring
  · rw [fexp]
    push_cast
    ring

/-! ### The kernel integral -/

/-- `∫₀¹ e(kα) dα = δ_{k,0}` for `k : ℤ`. -/
lemma integral_fexp_int_mul (k : ℤ) :
    ∫ α in (0:ℝ)..1, fexp ((k : ℝ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, fexp]
  · have hk' : (2 * Real.pi * Complex.I * k) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero, hk]
    have hanti : ∀ α : ℝ, HasDerivAt (fun α => fexp ((k : ℝ) * α) / (2 * Real.pi * Complex.I * k))
        (fexp ((k : ℝ) * α)) α := by
      intro α
      have hcast : (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 2 * Real.pi * Complex.I * k := by
        push_cast
        ring
      have h := (hasDerivAt_fexp ((k : ℝ)) α).div_const (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ))
      rw [hcast, mul_div_cancel_right₀ _ hk'] at h
      exact h
    have hcont : Continuous fun α : ℝ => fexp ((k : ℝ) * α) / (2 * Real.pi * Complex.I * k) :=
      (fexp_mul_continuous _).div_const _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (fun α _ => hanti α) ((fexp_mul_continuous _).intervalIntegrable _ _)
    rw [hftc]
    have he1 : fexp ((k : ℝ) * (1 : ℝ)) = 1 := by
      rw [mul_one]
      exact fexp_int_one k
    rw [he1, mul_zero, fexp_zero, if_neg hk, sub_self]

/-! ### Trigonometric polynomials and Parseval -/

/-- The trigonometric sum `S(α) = ∑_{n ∈ s} aₙ e(nα)`. -/
noncomputable def trigSum (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ s, a n * fexp (n * α)

lemma hasDerivAt_trigTerm (a : ℕ → ℂ) (n : ℕ) (α : ℝ) :
    HasDerivAt (fun α => a n * fexp ((n : ℝ) * α))
      (a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n))) α := by
  simpa using (hasDerivAt_fexp ((n : ℝ)) α).const_mul (a n)

lemma trigSum_hasDerivAt (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) :
    HasDerivAt (trigSum a s)
      (∑ n ∈ s, a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n))) α := by
  change HasDerivAt (fun β => ∑ n ∈ s, a n * fexp ((n : ℝ) * β)) _ α
  apply HasDerivAt.fun_sum
  intro n hn
  exact hasDerivAt_trigTerm a n α

lemma trigSum_continuous (a : ℕ → ℂ) (s : Finset ℕ) : Continuous (trigSum a s) := by
  apply continuous_finsetSum
  intro n _
  exact (fexp_mul_continuous _).const_mul _

lemma trigSum_deriv_continuous (a : ℕ → ℂ) (s : Finset ℕ) :
    Continuous fun α => ∑ n ∈ s, a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n)) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul ((fexp_mul_continuous _).mul continuous_const)

/-- The product expansion: `S·star S = ∑_{n,m} aₙ (star aₘ) e((n-m)α)`. -/
lemma trigSum_mul_star (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) :
    (trigSum a s α) * star (trigSum a s α) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α) := by
  rw [trigSum, star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [star_mul, star_fexp]
  calc (a n * fexp ((n : ℝ) * α)) * (fexp (-((m : ℝ) * α)) * star (a m))
      = (a n * star (a m)) * (fexp ((n : ℝ) * α) * fexp (-((m : ℝ) * α))) := by ring_nf
    _ = (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α) := by
        rw [← fexp_add]
        congr 1
        push_cast
        ring_nf

/-- Parseval for trigonometric polynomials: `∫₀¹ S·star S = ∑ aₙ (star aₙ)`. -/
lemma integral_trigSum_mul_star (a : ℕ → ℂ) (s : Finset ℕ) :
    ∫ α in (0:ℝ)..1, (trigSum a s α) * star (trigSum a s α) =
      ∑ n ∈ s, a n * star (a n) := by
  have hterm : ∀ n m : ℕ, IntervalIntegrable
      (fun α => (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α)) MeasureTheory.volume 0 1 := by
    intro n m
    exact ((fexp_mul_continuous _).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun α _ => trigSum_mul_star a s α)]
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    (continuous_finsetSum _ fun m _ => ((fexp_mul_continuous _).const_mul _)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum fun m _ => hterm n m]
  rw [Finset.sum_eq_single n]
  · rw [intervalIntegral.integral_const_mul]
    rw [show (↑(n : ℤ) - ↑n : ℝ) = 0 by norm_num]
    simp
  · intro m _ hm
    rw [intervalIntegral.integral_const_mul]
    have hmn : (n : ℤ) - m ≠ 0 := by omega
    rw [show ((n : ℤ) - m : ℝ) = (((n : ℤ) - m : ℤ) : ℝ) by norm_num,
      integral_fexp_int_mul, if_neg hmn]
    simp
  · intro hn'
    exact (hn' hn).elim

/-- Parseval (real form): `∫₀¹ ‖S‖² = ∑ ‖aₙ‖²`. -/
lemma integral_trigSum_norm_sq (a : ℕ → ℂ) (s : Finset ℕ) :
    ∫ α in (0:ℝ)..1, ‖trigSum a s α‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h1 : ∀ α : ℝ, ‖trigSum a s α‖ ^ 2 = ((trigSum a s α) * star (trigSum a s α)).re := by
    intro α
    rw [show star (trigSum a s α) = conj (trigSum a s α) from rfl,
      ← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
  have hint : IntervalIntegrable (fun α => (trigSum a s α) * star (trigSum a s α))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul _ (continuous_star.comp _)
    all_goals
      apply continuous_finsetSum
      intro n _
      exact (fexp_mul_continuous _).const_mul _
  have h2 : (∑ n ∈ s, a n * star (a n)) = ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show star (a n) = conj (a n) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ∫ α in (0:ℝ)..1, ((trigSum a s α) * star (trigSum a s α)).re =
      (∫ α in (0:ℝ)..1, (trigSum a s α) * star (trigSum a s α)).re := by
    exact Complex.reCLM.intervalIntegral_comp_comm hint
  rw [intervalIntegral.integral_congr (fun α _ => h1 α), h3, integral_trigSum_mul_star, h2,
    Complex.ofReal_re]

/-! ### Arc machinery: separated arcs in a period window -/

/-- The arcs of radius `δ/2` about pairwise `δ`-separated centers, all contained
in the window `Ioc ρ (ρ+1)`, have total `g`-mass at most that of one period. -/
lemma sum_integral_arcs_le {ι : Type*} {s : Finset ι} {c : ι → ℝ} {δ : ℝ} (_hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |c i - c j|)
    {ρ : ℝ} (harc : ∀ i ∈ s, ρ + δ / 2 ≤ c i ∧ c i ≤ ρ + 1 - δ / 2)
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀ x, 0 ≤ g x) (hper : Function.Periodic g 1) :
    ∑ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t ≤ ∫ t in Set.Ioc 0 1, g t := by
  classical
  set W := Set.Ioc ρ (ρ + 1) with hW
  have hJW : ∀ i ∈ s, Set.Ioc (c i - δ / 2) (c i + δ / 2) ⊆ W := by
    intro i hi
    apply Set.Ioc_subset_Ioc
    · linarith [(harc i hi).1]
    · linarith [(harc i hi).2]
  have hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Set.Ioc (c i - δ / 2) (c i + δ / 2)) (Set.Ioc (c j - δ / 2) (c j + δ / 2)) := by
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases le_total (c i) (c j) with hle | hle
    · have h := hsep i hi j hj hij
      rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
      linarith [hxi.2, hxj.1]
    · have h := hsep i hi j hj hij
      rw [abs_of_nonneg (sub_nonneg.mpr hle)] at h
      linarith [hxi.1, hxj.2]
  have hInt : ∀ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t =
      ∫ t in W, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t := by
    intro i hi
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_self_of_subset_right (hJW i hi)]
  have hsumint : IntegrableOn (fun x => ∑ i ∈ s,
      (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g x) W := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (hg.integrableOn_Ioc.indicator measurableSet_Ioc)
  have hpoint : ∀ x ∈ W, (∑ i ∈ s, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g x) ≤ g x := by
    intro x hx
    by_cases h : ∃ i ∈ s, x ∈ Set.Ioc (c i - δ / 2) (c i + δ / 2)
    · obtain ⟨i, hi, hxi⟩ := h
      rw [Finset.sum_eq_single i
        (fun j hj hjne => Set.indicator_of_notMem
          (Set.disjoint_left.mp (hdisj i hi j hj hjne.symm) hxi) g)
        (fun hi' => (hi' hi).elim)]
      exact (Set.indicator_of_mem hxi g).le
    · push Not at h
      rw [Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (h i hi) g]
      exact hgn x
  calc ∑ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t
      = ∑ i ∈ s, ∫ t in W, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t :=
        Finset.sum_congr rfl fun i hi => hInt i hi
    _ = ∫ t in W, ∑ i ∈ s, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t := by
        exact (MeasureTheory.integral_finsetSum s
          (fun i _ => (hg.integrableOn_Ioc.indicator measurableSet_Ioc))).symm
    _ ≤ ∫ t in W, g t :=
        MeasureTheory.setIntegral_mono_on hsumint hg.integrableOn_Ioc measurableSet_Ioc hpoint
    _ = ∫ t in Set.Ioc 0 1, g t := by
        rw [← intervalIntegral.integral_of_le (by linarith : ρ ≤ ρ + 1),
          hper.intervalIntegral_add_eq ρ 0, zero_add,
          intervalIntegral.integral_of_le (zero_le_one)]

/-- The window shift: for a `1`-periodic `g`, the integral over an arc of radius
`δ/2` equals that over the arc shifted by `1`. -/
lemma integral_arc_shift {g : ℝ → ℝ} (hper : Function.Periodic g 1) (y δ : ℝ)
    (hδ : 0 ≤ δ) :
    ∫ t in Set.Ioc (y - δ / 2) (y + δ / 2), g t =
      ∫ t in Set.Ioc (y + 1 - δ / 2) (y + 1 + δ / 2), g t := by
  rw [← intervalIntegral.integral_of_le (by linarith : y - δ / 2 ≤ y + δ / 2),
    ← intervalIntegral.integral_of_le (by linarith : y + 1 - δ / 2 ≤ y + 1 + δ / 2)]
  calc
    ∫ x in (y - δ / 2)..(y + δ / 2), g x =
        ∫ x in (y - δ / 2)..(y + δ / 2), g (x + 1) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact (hper x).symm
    _ = ∫ x in (y - δ / 2 + 1)..(y + δ / 2 + 1), g x :=
      intervalIntegral.integral_comp_add_right g 1
    _ = ∫ x in (y + 1 - δ / 2)..(y + 1 + δ / 2), g x := by
      congr 1 <;> ring

/-- If a finite set of points of `[0,1)` is pairwise at distance in `[δ, 1-δ]`,
then all arcs of radius `δ/2` about the points shifted by `1` fit inside a
common window `(ρ, ρ+1)` (the `ρ` is the midpoint of the wrap-around gap). -/
lemma exists_window {s : Finset ℝ} (hs : s.Nonempty) {δ : ℝ} (_hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| ∧ |x - y| ≤ 1 - δ) :
    ∃ ρ : ℝ, ∀ x ∈ s, ρ + δ / 2 ≤ x + 1 ∧ x + 1 ≤ ρ + 1 - δ / 2 := by
  classical
  set ymin := s.min' hs
  set ymax := s.max' hs
  have hgap : ymax - ymin ≤ 1 - δ := by
    rcases eq_or_ne ymin ymax with heq | hne
    · linarith [heq, hδ1]
    · have h1 := hsep ymin (s.min'_mem hs) ymax (s.max'_mem hs) hne
      have h2 : |ymax - ymin| = ymax - ymin := abs_of_nonneg (by
        have := s.min'_le ymax (s.max'_mem hs); linarith)
      rw [abs_sub_comm, h2] at h1
      exact h1.2
  refine ⟨(ymax + ymin + 1) / 2, fun x hx => ?_⟩
  have hmin := s.min'_le x hx
  have hmax := s.le_max' x hx
  constructor <;> linarith

/-! ### Farey separation -/

/-- Reduced fractions are unique: coprime `bᵢ/qᵢ` with equal values coincide. -/
lemma farey_inj {q₁ q₂ b₁ b₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hb₁ : b₁.Coprime q₁) (hb₂ : b₂.Coprime q₂)
    (h : (b₁ : ℝ) / q₁ = (b₂ : ℝ) / q₂) :
    q₁ = q₂ ∧ b₁ = b₂ := by
  have hcross : (b₁ : ℤ) * q₂ = (b₂ : ℤ) * q₁ := by
    have hq₁' : (q₁ : ℝ) ≠ 0 := by positivity
    have hq₂' : (q₂ : ℝ) ≠ 0 := by positivity
    have h1 : (b₁ : ℝ) * q₂ = (b₂ : ℝ) * q₁ := by
      field_simp at h
      linarith [h]
    exact_mod_cast h1
  have hq1q2 : q₁ ∣ q₂ := by
    have : q₁ ∣ b₁ * q₂ := by
      have h2 : (b₂ : ℤ) * q₁ = (b₁ : ℤ) * q₂ := hcross.symm
      have h3 : (b₂ : ℕ) * q₁ = b₁ * q₂ := by exact_mod_cast h2
      rw [← h3]
      exact dvd_mul_left q₁ b₂
    exact hb₁.symm.dvd_of_dvd_mul_left this
  have hq2q1 : q₂ ∣ q₁ := by
    have : q₂ ∣ b₂ * q₁ := by
      have h3 : (b₁ : ℕ) * q₂ = b₂ * q₁ := by exact_mod_cast hcross
      rw [← h3]
      exact dvd_mul_left q₂ b₁
    exact hb₂.symm.dvd_of_dvd_mul_left this
  have hqq : q₁ = q₂ := Nat.dvd_antisymm hq1q2 hq2q1
  refine ⟨hqq, ?_⟩
  have h3 : (b₁ : ℕ) * q₂ = b₂ * q₁ := by exact_mod_cast hcross
  rw [hqq] at h3
  exact Nat.eq_of_mul_eq_mul_right hq₂ h3

/-- Farey fractions of order `X` are `1/X²`-separated, also across `0`. -/
lemma farey_sep {X : ℕ} (hX : 1 ≤ X) {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁ ∧ q₁ ≤ X)
    (hq₂ : 1 ≤ q₂ ∧ q₂ ≤ X) {b₁ b₂ : ℕ} (_hb₁ : b₁.Coprime q₁) (_hb₂ : b₂.Coprime q₂)
    (hb₁' : b₁ < q₁) (hb₂' : b₂ < q₂)
    (hne : (b₁ : ℝ) / q₁ ≠ (b₂ : ℝ) / q₂) :
    1 / (X : ℝ) ^ 2 ≤ |(b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂| ∧
      |(b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂| ≤ 1 - 1 / (X : ℝ) ^ 2 := by
  have hq₁0 : (0:ℝ) < q₁ := by exact_mod_cast hq₁.1
  have hq₂0 : (0:ℝ) < q₂ := by exact_mod_cast hq₂.1
  have hqprod : (0:ℝ) < (q₁ : ℝ) * q₂ := mul_pos hq₁0 hq₂0
  have hcross : (b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂ =
      ((b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁) / ((q₁ : ℝ) * q₂) := by field_simp
  have hne_int : (b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁ ≠ 0 := by
    intro h
    apply hne
    have h1 : ((b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁) = 0 := by exact_mod_cast h
    have h2 : (b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂ = 0 := by
      rw [hcross, h1, zero_div]
    linarith
  have habs1 : (1:ℝ) ≤ |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| := by
    have h1 : (1:ℤ) ≤ |(b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁| := by
      exact Int.one_le_abs hne_int
    exact_mod_cast h1
  have hub_int : |(b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁| ≤ (q₁ : ℤ) * q₂ - 1 := by
    have hb1nat : b₁ * q₂ < q₁ * q₂ :=
      Nat.mul_lt_mul_of_pos_right hb₁' (by omega)
    have hb2nat : b₂ * q₁ < q₁ * q₂ := by
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hb₂' (by omega : 0 < q₁)
    have hb1 : (b₁ : ℤ) * q₂ < (q₁ : ℤ) * q₂ := by exact_mod_cast hb1nat
    have hb2 : (b₂ : ℤ) * q₁ < (q₁ : ℤ) * q₂ := by exact_mod_cast hb2nat
    have hpos1 : (0 : ℤ) ≤ (b₁ : ℤ) * q₂ := by positivity
    have hpos2 : (0 : ℤ) ≤ (b₂ : ℤ) * q₁ := by positivity
    rw [abs_le]
    constructor <;> omega
  have hub : |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| ≤ (q₁ : ℝ) * q₂ - 1 := by
    exact_mod_cast hub_int
  have hqX : (q₁ : ℝ) * q₂ ≤ (X : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul (by exact_mod_cast hq₁.2) (by exact_mod_cast hq₂.2)
      (by positivity) (by positivity)
  rw [hcross, abs_div, abs_of_pos hqprod]
  constructor
  · rw [le_div_iff₀ hqprod]
    calc 1 / (X : ℝ) ^ 2 * ((q₁ : ℝ) * q₂) ≤ 1 / (X : ℝ) ^ 2 * (X : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hqX (by positivity)
      _ = 1 := by field_simp
      _ ≤ |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| := habs1
  · rw [div_le_iff₀ hqprod]
    calc |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| ≤ (q₁ : ℝ) * q₂ - 1 := hub
      _ ≤ (1 - 1 / (X : ℝ) ^ 2) * ((q₁ : ℝ) * q₂) := by
          have h3 : (q₁ : ℝ) * q₂ / (X : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity : (0:ℝ) < (X:ℝ)^2)]
            exact hqX
          have h4 : (1 - 1 / (X : ℝ) ^ 2) * ((q₁ : ℝ) * q₂) =
              (q₁ : ℝ) * q₂ - (q₁ : ℝ) * q₂ / (X : ℝ) ^ 2 := by
            field_simp
          rw [h4]
          linarith [h3, hqprod]

/-! ### The additive large sieve (inequality (4) of the paper) -/

lemma trigSum_periodic (a : ℕ → ℂ) (s : Finset ℕ) : Function.Periodic (trigSum a s) 1 := by
  intro α
  rw [trigSum, trigSum]
  apply Finset.sum_congr rfl
  intro n _
  have h : (n : ℝ) * (α + 1) = n * α + n := by ring
  rw [h, fexp_add]
  have hn : fexp (n : ℝ) = 1 := by
    simpa using fexp_int_one (n : ℤ)
  rw [hn, mul_one]

/-- **The additive large sieve** (inequality (4) of Chen's paper):
`∑_{q ≤ X} ∑_{(b,q)=1} |S(b/q)|² ≤ (X² + πN) ∑|aₙ|²`. -/
theorem additive_large_sieve (X M N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
        ‖trigSum a (Finset.Ioc M (M + N)) ((b : ℝ) / q)‖ ^ 2
      ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  set s := Finset.Ioc M (M + N)
  set Z := ∑ n ∈ s, ‖a n‖ ^ 2
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun n _ => by positivity
  rcases eq_zero_or_pos X with rfl | hX
  · simp only [Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty]
    positivity
  rcases eq_zero_or_pos N with rfl | hN
  · have : s = ∅ := by simp [s]
    simp [this, Z, trigSum]
  -- The shifted sum and its derivative.
  set c := M + (N + 1) / 2 with hc_def
  set S := trigSum a s with hS_def
  set b : ℕ → ℂ := fun n => (2 * Real.pi * Complex.I * ((n : ℤ) - c)) * a n
    with hb_def
  set U := trigSum b s with hU_def
  set g : ℝ → ℂ := fun α => fexp (-(c : ℝ) * α) with hg_def
  set T : ℝ → ℂ := fun α =>
    ∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) with hT_def
  set T' : ℝ → ℂ := fun α =>
    ∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ))) with hT'_def
  have hTderiv : ∀ α, HasDerivAt T (T' α) α := by
    intro α
    rw [hT_def, hT'_def]
    apply HasDerivAt.fun_sum
    intro n hn
    simpa using
      (hasDerivAt_fexp ((((n : ℤ) - c : ℤ) : ℝ)) α).const_mul (a n)
  have hT'cont : Continuous T' := by
    rw [hT'_def]
    apply continuous_finsetSum
    intro n hn
    exact continuous_const.mul ((fexp_mul_continuous _).mul continuous_const)
  have hTcont : Continuous T := by
    rw [hT_def]
    apply continuous_finsetSum
    intro n hn
    exact (fexp_mul_continuous _).const_mul _
  have hTfactor : ∀ α, T α = g α * S α := by
    intro α
    rw [hT_def, hg_def, hS_def, trigSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hphase : fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) =
        fexp (-(c : ℝ) * α) * fexp ((n : ℝ) * α) := by
      rw [← fexp_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  have hT'factor : ∀ α, T' α = g α * U α := by
    intro α
    rw [hT'_def, hg_def, hU_def, trigSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hphase : fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) =
        fexp (-(c : ℝ) * α) * fexp ((n : ℝ) * α) := by
      rw [← fexp_add]
      congr 1
      push_cast
      ring
    rw [hb_def, hphase]
    push_cast
    ring
  have hTper : Function.Periodic T 1 := by
    intro α
    change (∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * (α + 1))) =
      ∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * α)
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun z => a n * z) (fexp_periodic_mul ((n : ℤ) - c) α)
  have hT'per : Function.Periodic T' 1 := by
    intro α
    change (∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * (α + 1)) *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ)))) =
      ∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) *
        (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ)))
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun z => a n * (z *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ))))
      (fexp_periodic_mul ((n : ℤ) - c) α)
  have hTnorm : ∀ α, ‖T α‖ = ‖S α‖ := by
    intro α
    rw [hTfactor, norm_mul, hg_def, fexp_norm, one_mul]
  have hT'norm : ∀ α, ‖T' α‖ = ‖U α‖ := by
    intro α
    rw [hT'factor, norm_mul, hg_def, fexp_norm, one_mul]
  have hg1per : Function.Periodic (fun α => ‖T α‖ ^ 2) 1 := by
    intro α
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hTper α)
  have hg2per : Function.Periodic (fun α => ‖T α‖ * ‖T' α‖) 1 := by
    intro α
    exact congrArg₂ (fun z w : ℂ => ‖z‖ * ‖w‖) (hTper α) (hT'per α)
  -- Parseval for `S` and `U`.
  have hPS : ∫ α in (0:ℝ)..1, ‖S α‖ ^ 2 = Z := integral_trigSum_norm_sq a s
  have hPU : ∫ α in (0:ℝ)..1, ‖U α‖ ^ 2 ≤ Real.pi ^ 2 * N ^ 2 * Z := by
    rw [integral_trigSum_norm_sq]
    have hterm : ∀ n ∈ s, ‖b n‖ ^ 2 ≤ (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
      intro n hn
      have hnk : |((n : ℤ) - c : ℝ)| ≤ N / 2 := by
        rw [Finset.mem_Ioc] at hn
        have hupper_int : (2 : ℤ) * ((n : ℤ) - c) ≤ N := by
          omega
        have hlower_int : -(N : ℤ) ≤ 2 * ((n : ℤ) - c) := by
          omega
        have h1 : (((n : ℤ) - c : ℤ) : ℝ) ≤ N / 2 := by
          have hupper_real : (2 : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) ≤ N := by
            exact_mod_cast hupper_int
          linarith
        have h2 : -(N / 2 : ℝ) ≤ (((n : ℤ) - c : ℤ) : ℝ) := by
          have hlower_real : -(N : ℝ) ≤ 2 * (((n : ℤ) - c : ℤ) : ℝ) := by
            exact_mod_cast hlower_int
          linarith
        push_cast at h1 h2
        rw [abs_le]
        exact ⟨h2, h1⟩
      have hbnorm : ‖b n‖ = 2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖ := by
        rw [hb_def, norm_mul, norm_mul]
        have h2pi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
          rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        have h2piI : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
          rw [norm_mul, h2pi, Complex.norm_I, mul_one]
        have hnc : ‖((n : ℤ) : ℂ) - (c : ℂ)‖ =
            |((n : ℤ) : ℝ) - (c : ℝ)| := by
          calc
            ‖((n : ℤ) : ℂ) - (c : ℂ)‖ =
                ‖((((n : ℤ) - (c : ℤ) : ℤ)) : ℂ)‖ := by
                  congr 2
                  push_cast
                  rfl
            _ = |((((n : ℤ) - (c : ℤ) : ℤ)) : ℝ)| :=
              Complex.norm_intCast _
            _ = |((n : ℤ) : ℝ) - (c : ℝ)| := by
              push_cast
              rfl
        rw [h2piI, hnc]
      rw [hbnorm]
      have h1 : (2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖) ^ 2 ≤
          (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
        have h2 : 2 * Real.pi * |((n : ℤ) - c : ℝ)| ≤ Real.pi * N := by
          nlinarith [mul_le_mul_of_nonneg_left hnk Real.pi_pos.le]
        calc (2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖) ^ 2
            = (2 * Real.pi * |((n : ℤ) - c : ℝ)|) ^ 2 * ‖a n‖ ^ 2 := by ring
          _ ≤ (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
              have hsquare : (2 * Real.pi * |((n : ℤ) - c : ℝ)|) ^ 2 ≤
                  (Real.pi * N) ^ 2 :=
                (sq_le_sq₀ (by positivity) (by positivity)).2 h2
              exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg ‖a n‖)
      exact h1
    calc ∑ n ∈ s, ‖b n‖ ^ 2 ≤ ∑ n ∈ s, (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 :=
        Finset.sum_le_sum hterm
      _ = (Real.pi * N) ^ 2 * Z := by rw [Finset.mul_sum]
      _ = Real.pi ^ 2 * N ^ 2 * Z := by ring
  -- The Farey points and their separation.
  set points := (Finset.Icc 1 X).sigma fun q => (Finset.range q).filter (·.Coprime q)
    with hpoints_def
  set y : (Σ q : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / (p.1 : ℝ)
  set δ := 1 / (X : ℝ) ^ 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ_def, div_le_one (by positivity : (0:ℝ) < (X:ℝ)^2)]
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    nlinarith
  have hmem : (⟨1, 0⟩ : Σ q : ℕ, ℕ) ∈ points := by
    rw [Finset.mem_sigma]
    have hX1 : 1 ≤ X := by omega
    exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX1⟩, by simp⟩
  have hpoints_ne : points.Nonempty := ⟨_, hmem⟩
  have hy_lt : ∀ p ∈ points, 0 ≤ y p ∧ y p < 1 := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hq, hb⟩ := hp
    rw [Finset.mem_filter] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Finset.mem_range] at hb1
    rw [Finset.mem_Icc] at hq
    have hq0 : (0:ℝ) < p.1 := by
      have : 1 ≤ p.1 := hq.1
      positivity
    constructor
    · positivity
    · rw [div_lt_one hq0]
      exact_mod_cast hb1
  have hy_ne : ∀ p ∈ points, ∀ p' ∈ points, p ≠ p' → y p ≠ y p' := by
    intro p hp p' hp' hpp'
    rw [Finset.mem_sigma] at hp hp'
    intro heq
    apply hpp'
    rw [Finset.mem_filter] at *
    obtain ⟨hq1, hb1⟩ := hp
    obtain ⟨hq2, hb2⟩ := hp'
    rw [Finset.mem_Icc] at hq1 hq2
    rw [Finset.mem_range] at *
    obtain ⟨h1, h2⟩ := farey_inj (by omega : 0 < p.1) (by omega : 0 < p'.1) hb1.2 hb2.2 heq
    rcases p with ⟨q, b⟩
    rcases p' with ⟨q', b'⟩
    simp only at h1 h2 ⊢
    subst q'
    subst b'
    rfl
  have hy_sep : ∀ p ∈ points, ∀ p' ∈ points, p ≠ p' →
      δ ≤ |y p - y p'| ∧ |y p - y p'| ≤ 1 - δ := by
    intro p hp p' hp' hpp'
    rw [Finset.mem_sigma] at hp hp'
    obtain ⟨hq1, hb1⟩ := hp
    obtain ⟨hq2, hb2⟩ := hp'
    rw [Finset.mem_filter] at hb1 hb2
    rw [Finset.mem_Icc] at hq1 hq2
    rw [Finset.mem_range] at *
    have := farey_sep hX hq1 hq2 hb1.2 hb2.2 hb1.1 hb2.1 (hy_ne p (by
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_Icc.mpr hq1,
        Finset.mem_filter.mpr ⟨by simpa using hb1.1, hb1.2⟩⟩) p' (by
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_Icc.mpr hq2,
        Finset.mem_filter.mpr ⟨by simpa using hb2.1, hb2.2⟩⟩) hpp')
    rw [hδ_def]
    exact this
  -- The window for the lifted arcs.
  set pts := points.image y with hpts_def
  have hpts_ne : pts.Nonempty := hpoints_ne.image y
  obtain ⟨ρ, hρ⟩ := exists_window hpts_ne hδ hδ1 (by
    intro x₁ hx₁ x₂ hx₂ hne
    rw [Finset.mem_image] at hx₁ hx₂
    obtain ⟨p₁, hp₁, rfl⟩ := hx₁
    obtain ⟨p₂, hp₂, rfl⟩ := hx₂
    have hpp : p₁ ≠ p₂ := fun h => hne (h ▸ rfl)
    exact hy_sep p₁ hp₁ p₂ hp₂ hpp)
  -- Gallagher per point.
  have hgal : ∀ p ∈ points, ‖T (y p)‖ ^ 2 ≤
      δ⁻¹ * (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2) +
        (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖) := by
    intro p hp
    have h := gallagher_centered hTderiv hT'cont hδ (y p)
    rwa [intervalIntegral.integral_of_le (by linarith : y p - δ / 2 ≤ y p + δ / 2),
      intervalIntegral.integral_of_le (by linarith : y p - δ / 2 ≤ y p + δ / 2)] at h
  -- Shift arcs by `1` and sum.
  have harcs1 : ∑ p ∈ points, ∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2 ≤
      ∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun p hp => integral_arc_shift hg1per (y p) δ hδ.le)]
    exact sum_integral_arcs_le hδ (fun i hi j hj hij => by
      have := hy_sep i hi j hj hij
      have h1 : |y i + 1 - (y j + 1)| = |y i - y j| := by
        rw [show y i + 1 - (y j + 1) = y i - y j by ring]
      rw [h1]
      exact this.1) (fun i hi => by
      have hyi : y i ∈ pts := Finset.mem_image_of_mem y hi
      exact hρ (y i) hyi) (by
      exact hTcont.norm.pow 2) (fun x => by positivity) hg1per
  have harcs2 : ∑ p ∈ points, ∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖ ≤
      ∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖ := by
    rw [Finset.sum_congr rfl (fun p hp => integral_arc_shift hg2per (y p) δ hδ.le)]
    exact sum_integral_arcs_le hδ (fun i hi j hj hij => by
      have := hy_sep i hi j hj hij
      have h1 : |y i + 1 - (y j + 1)| = |y i - y j| := by
        rw [show y i + 1 - (y j + 1) = y i - y j by ring]
      rw [h1]
      exact this.1) (fun i hi => by
      have hyi : y i ∈ pts := Finset.mem_image_of_mem y hi
      exact hρ (y i) hyi) (by
      exact hTcont.norm.mul hT'cont.norm) (fun x => by positivity) hg2per
  -- AM–GM on the cross term.
  have hlam : (0:ℝ) < Real.pi * N := by positivity
  have hamgm : (∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖) ≤
      (Real.pi * N / 2) * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
        (2 * Real.pi * N)⁻¹ * (∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2) := by
    have hpt : ∀ t : ℝ, ‖T t‖ * ‖T' t‖ ≤
        (Real.pi * N / 2) * ‖T t‖ ^ 2 + (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2 := by
      intro t
      have h1 : (Real.pi * N / 2) * ‖T t‖ ^ 2 + (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2 -
          ‖T t‖ * ‖T' t‖ =
          (Real.pi * N / 2) * (‖T t‖ - ‖T' t‖ / (Real.pi * N)) ^ 2 := by
        field_simp
        ring
      have h2 : 0 ≤ (Real.pi * N / 2) * (‖T t‖ - ‖T' t‖ / (Real.pi * N)) ^ 2 := by positivity
      linarith [h2]
    have hint1 : IntegrableOn (fun t => ‖T t‖ * ‖T' t‖) (Set.Ioc 0 1) :=
      (hTcont.norm.mul hT'cont.norm).integrableOn_Ioc
    have hint2a : IntegrableOn (fun t => (Real.pi * N / 2) * ‖T t‖ ^ 2) (Set.Ioc 0 1) :=
      ((hTcont.norm.pow 2).const_mul _).integrableOn_Ioc
    have hint2b : IntegrableOn (fun t => (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2) (Set.Ioc 0 1) :=
      ((hT'cont.norm.pow 2).const_mul _).integrableOn_Ioc
    calc
      ∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖ ≤
          ∫ t in Set.Ioc 0 1, ((Real.pi * N / 2) * ‖T t‖ ^ 2 +
            (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2) :=
        MeasureTheory.setIntegral_mono_on hint1 (hint2a.add hint2b)
          measurableSet_Ioc (fun x _ => hpt x)
      _ = (Real.pi * N / 2) * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
          (2 * Real.pi * N)⁻¹ * (∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2) := by
        rw [MeasureTheory.integral_add hint2a hint2b, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
  have hPS' : ∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2 = Z := by
    rw [← intervalIntegral.integral_of_le (zero_le_one)]
    calc
      ∫ α in (0 : ℝ)..1, ‖T α‖ ^ 2 = ∫ α in (0 : ℝ)..1, ‖S α‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        exact congrArg (fun z : ℝ => z ^ 2) (hTnorm α)
      _ = Z := hPS
  have hPU' : ∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2 ≤ Real.pi ^ 2 * N ^ 2 * Z := by
    rw [← intervalIntegral.integral_of_le (zero_le_one)]
    calc
      ∫ α in (0 : ℝ)..1, ‖T' α‖ ^ 2 = ∫ α in (0 : ℝ)..1, ‖U α‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        exact congrArg (fun z : ℝ => z ^ 2) (hT'norm α)
      _ ≤ Real.pi ^ 2 * N ^ 2 * Z := hPU
  -- Final assembly.
  have hmain : ∑ p ∈ points, ‖T (y p)‖ ^ 2 ≤ ((X : ℝ) ^ 2 + Real.pi * N) * Z := by
    calc ∑ p ∈ points, ‖T (y p)‖ ^ 2
        ≤ ∑ p ∈ points, (δ⁻¹ *
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2) +
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖)) :=
          Finset.sum_le_sum hgal
      _ = δ⁻¹ * (∑ p ∈ points,
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2)) +
          (∑ p ∈ points,
            (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ δ⁻¹ * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
          (∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖) := by
          exact add_le_add (mul_le_mul_of_nonneg_left harcs1 (inv_nonneg.mpr hδ.le)) harcs2
      _ ≤ δ⁻¹ * Z + ((Real.pi * N / 2) * Z + (2 * Real.pi * N)⁻¹ * (Real.pi ^ 2 * N ^ 2 * Z)) := by
          rw [hPS']
          apply add_le_add le_rfl
          have hc1 : 0 ≤ Real.pi * N / 2 := by positivity
          have hc2 : 0 ≤ (2 * Real.pi * N)⁻¹ := by positivity
          exact hamgm.trans (add_le_add
            (mul_le_mul_of_nonneg_left hPS'.le hc1)
            (mul_le_mul_of_nonneg_left hPU' hc2))
      _ = ((X : ℝ) ^ 2 + Real.pi * N) * Z := by
          rw [hδ_def]
          field_simp [hX.ne', hN.ne', Real.pi_ne_zero]
          ring
  have hST : ∀ p ∈ points, ‖S (y p)‖ ^ 2 = ‖T (y p)‖ ^ 2 := by
    intro p hp
    rw [← hTnorm (y p)]
  calc
    ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
        ‖S ((b : ℝ) / q)‖ ^ 2 =
        ∑ p ∈ points, ‖S (y p)‖ ^ 2 := by
          rw [hpoints_def, Finset.sum_sigma]
    _ = ∑ p ∈ points, ‖T (y p)‖ ^ 2 :=
        Finset.sum_congr rfl hST
    _ ≤ ((X : ℝ) ^ 2 + Real.pi * N) * Z := hmain

end Chen.LargeSieve
