import ChenTheorem.Lemma9.BombieriVinogradov.TypeII
import ChenTheorem.Lemma6.Core

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Mellin separation of the Type-II hyperbola

The sharp condition `l*m ≤ x` cannot be replaced by a naive dyadic
staircase without a power loss.  This file starts the standard remedy using
the smoothing Mellin kernel already proved for Lemma 6.  On each rectangle,
the Mellin variable separates the two visible Vaughan factors exactly.
-/

/-- The visible left Vaughan coefficient with its Mellin phase. -/
noncomputable def typeIISpectralLeft
    (U : ℕ) (s : ℂ) (l : ℕ) : ℂ :=
  (vaughanTypeIILeftCoefficient U l : ℂ) / (l : ℂ) ^ s

/-- The von-Mangoldt coefficient with its Mellin phase. -/
noncomputable def typeIISpectralLambda
    (s : ℂ) (m : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt m : ℂ) / (m : ℂ) ^ s

/-- On a nonnegative real line, division by `n^s` cannot increase the
visible left Vaughan coefficient. -/
theorem norm_typeIISpectralLeft_le
    (U n : ℕ) (s : ℂ) (hn : 1 ≤ n) (hs : 0 ≤ s.re) :
    ‖typeIISpectralLeft U s n‖ ≤
      ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ := by
  unfold typeIISpectralLeft
  rw [norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos
    (by exact_mod_cast (show 0 < n by omega))]
  exact div_le_self (norm_nonneg _)
    (Real.one_le_rpow (by exact_mod_cast hn) hs)

/-- The same contraction for the von-Mangoldt factor. -/
theorem norm_typeIISpectralLambda_le
    (n : ℕ) (s : ℂ) (hn : 1 ≤ n) (hs : 0 ≤ s.re) :
    ‖typeIISpectralLambda s n‖ ≤
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
  unfold typeIISpectralLambda
  rw [norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos
    (by exact_mod_cast (show 0 < n by omega))]
  exact div_le_self (norm_nonneg _)
    (Real.one_le_rpow (by exact_mod_cast hn) hs)

/-- On an interval `(M,M+N]`, a Mellin line with real part at least one
contributes the essential reciprocal lower-endpoint factor. -/
theorem norm_typeIISpectralLeft_le_div
    (U M n : ℕ) (s : ℂ) (hM : 1 ≤ M) (hn : M < n) (hs : 1 ≤ s.re) :
    ‖typeIISpectralLeft U s n‖ ≤
      ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ / (M : ℝ) := by
  unfold typeIISpectralLeft
  rw [norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast (show 0 < n by omega))]
  have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hnbase hs
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast (show M ≤ n by omega)
  have hden : (M : ℝ) ≤ (n : ℝ) ^ s.re := hMn.trans hpow
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (by exact_mod_cast (show 0 < M by omega)) hden

theorem norm_typeIISpectralLambda_le_div
    (K n : ℕ) (s : ℂ) (hK : 1 ≤ K) (hn : K < n) (hs : 1 ≤ s.re) :
    ‖typeIISpectralLambda s n‖ ≤
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ / (K : ℝ) := by
  unfold typeIISpectralLambda
  rw [norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast (show 0 < n by omega))]
  have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hnbase hs
  have hKn : (K : ℝ) ≤ n := by exact_mod_cast (show K ≤ n by omega)
  have hden : (K : ℝ) ≤ (n : ℝ) ^ s.re := hKn.trans hpow
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (by exact_mod_cast (show 0 < K by omega)) hden

/-- The Mellin phase contracts the left coefficient square mean on every
positive interval. -/
theorem typeIISpectralLeft_sq_sum_le
    (U M N : ℕ) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑ n ∈ Finset.Ioc M (M + N),
        ‖typeIISpectralLeft U s n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_typeIISpectralLeft_le U n s
      (by have := (Finset.mem_Ioc.mp hn).1; omega) hs) 2

/-- The Mellin phase also contracts the von-Mangoldt square mean. -/
theorem typeIISpectralLambda_sq_sum_le
    (K L : ℕ) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑ n ∈ Finset.Ioc K (K + L),
        ‖typeIISpectralLambda s n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc K (K + L),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_typeIISpectralLambda_le n s
      (by have := (Finset.mem_Ioc.mp hn).1; omega) hs) 2

/-- Square-mean version retaining the reciprocal interval scale. -/
theorem typeIISpectralLeft_sq_sum_le_div
    (U M N : ℕ) (s : ℂ) (hM : 1 ≤ M) (hs : 1 ≤ s.re) :
    (∑ n ∈ Finset.Ioc M (M + N),
        ‖typeIISpectralLeft U s n‖ ^ 2) ≤
      (∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) / (M : ℝ) ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc M (M + N),
        ‖typeIISpectralLeft U s n‖ ^ 2) ≤
        ∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2 / (M : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_typeIISpectralLeft_le_div U M n s hM
          (Finset.mem_Ioc.mp hn).1 hs) 2
    _ = (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) /
        (M : ℝ) ^ 2 := by rw [Finset.sum_div]

theorem typeIISpectralLambda_sq_sum_le_div
    (K L : ℕ) (s : ℂ) (hK : 1 ≤ K) (hs : 1 ≤ s.re) :
    (∑ n ∈ Finset.Ioc K (K + L),
        ‖typeIISpectralLambda s n‖ ^ 2) ≤
      (∑ n ∈ Finset.Ioc K (K + L),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) / (K : ℝ) ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc K (K + L),
        ‖typeIISpectralLambda s n‖ ^ 2) ≤
        ∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2 / (K : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_typeIISpectralLambda_le_div K n s hK
          (Finset.mem_Ioc.mp hn).1 hs) 2
    _ = (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) /
        (K : ℝ) ^ 2 := by rw [Finset.sum_div]

/-- The separated Type-II Dirichlet polynomial on one pair of intervals. -/
noncomputable def typeIISpectralRectangle {q : ℕ}
    (U M N K L : ℕ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  characterIntervalSum M N (typeIISpectralLeft U s) χ *
    characterIntervalSum K L (typeIISpectralLambda s) χ

/-- The spectral rectangle is exactly the corresponding double character
sum. -/
theorem typeIISpectralRectangle_eq_bilinear {q : ℕ}
    (U M N K L : ℕ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    typeIISpectralRectangle U M N K L s χ =
      bilinearCharacterRectangle M N K L
        (typeIISpectralLeft U s) (typeIISpectralLambda s) χ := by
  rw [typeIISpectralRectangle,
    bilinearCharacterRectangle_eq_mul]

/-- The height-independent polynomial majorant delivered by the large sieve
for one Mellin-separated Type-II rectangle. -/
noncomputable def typeIISpectralRectangleMajorant
    (C₀ C₁ : ℝ) (D Q M N K L : ℕ) : ℝ :=
  (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
      ((C₁ * ((M + N : ℕ) : ℝ) *
        (Real.log ((M + N : ℕ) : ℝ)) ^ 3) / (M : ℝ) ^ 2)) *
    (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
      (((L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2) /
        (K : ℝ) ^ 2))

theorem typeIISpectralRectangleMajorant_nonneg
    {C₀ C₁ : ℝ} {D Q M N K L : ℕ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hD : 1 ≤ D) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hMN : 2 ≤ M + N) (hKL : 2 ≤ K + L) :
    0 ≤ typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L := by
  unfold typeIISpectralRectangleMajorant
  have hlogMN : 0 ≤ Real.log ((M + N : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + N by omega))
  have hlogKL : 0 ≤ Real.log ((K + L : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + L by omega))
  positivity

/-- Dyadic-conductor large-sieve estimate for a Mellin-separated Type-II
rectangle.  On `Re s ≥ 1`, the spectral weights retain the reciprocal-square
interval scales needed to cancel the outer Mellin factor. -/
theorem typeIISpectralRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U D Q M N K L : ℕ) (s : ℂ),
        1 ≤ s.re → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖typeIISpectralRectangle U M N K L s i.2‖) ^ 2 ≤
            typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIILeftCoefficient_sq_mean with ⟨C₁, hC₁, hleftMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U D Q M N K L s hs hD hDQ hM hK hMN hKL
  have hleftRaw :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 (M + N),
            ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 :=
        hleftMean U (M + N) hMN
  have hleft :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖typeIISpectralLeft U s n‖ ^ 2) ≤
        (C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3) / (M : ℝ) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖typeIISpectralLeft U s n‖ ^ 2) ≤
          (∑ n ∈ Finset.Ioc M (M + N),
            ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) /
              (M : ℝ) ^ 2 :=
        typeIISpectralLeft_sq_sum_le_div U M N s hM hs
      _ ≤ (C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3) / (M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hleftRaw (sq_nonneg _)
  have hlambdaRaw :
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
        (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
          ∑ _n ∈ Finset.Ioc K (K + L),
            (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hndata := Finset.mem_Ioc.mp hn
        have hnpos : 0 < n := by omega
        have hlogmono : Real.log (n : ℝ) ≤
            Real.log ((K + L : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hnpos)
            (by exact_mod_cast hndata.2)
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
          (ArithmeticFunction.vonMangoldt_le_log.trans hlogmono) 2
      _ = (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by simp
  have hlambda :
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖typeIISpectralLambda s n‖ ^ 2) ≤
        ((L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2) /
          (K : ℝ) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖typeIISpectralLambda s n‖ ^ 2) ≤
          (∑ n ∈ Finset.Ioc K (K + L),
            ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) /
              (K : ℝ) ^ 2 :=
        typeIISpectralLambda_sq_sum_le_div K L s hK hs
      _ ≤ ((L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2) /
          (K : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlambdaRaw (sq_nonneg _)
  have hbase := hbilinear D Q M N K L
    (typeIISpectralLeft U s) (typeIISpectralLambda s) hD hDQ
  have hleftNonneg : 0 ≤
      (C₁ * ((M + N : ℕ) : ℝ) *
        (Real.log ((M + N : ℕ) : ℝ)) ^ 3) / (M : ℝ) ^ 2 :=
    (Finset.sum_nonneg fun n _ => sq_nonneg _).trans hleft
  have hbound := hbase.trans (by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hleft
        (mul_nonneg hC₀.le (by positivity))
    · exact mul_le_mul_of_nonneg_left hlambda
        (mul_nonneg hC₀.le (by positivity))
    · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
        (Finset.sum_nonneg fun n _ => sq_nonneg _)
    · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
        hleftNonneg)
  simpa only [typeIISpectralRectangleMajorant,
    typeIISpectralRectangle, norm_mul, mul_assoc] using hbound

/-- Positive-real complex powers split the quotient `x/(l*m)` into the
two Mellin phases used by the spectral rectangle. -/
theorem typeII_nat_quotient_cpow_factor
    (x l m : ℕ) (s : ℂ) :
    (((x : ℝ) / ((l : ℝ) * m) : ℝ) : ℂ) ^ s =
      (x : ℂ) ^ s / ((l : ℂ) ^ s * (m : ℂ) ^ s) := by
  convert Chen.lemma6_nat_quotient_cpow_factor x m (l, 1) s using 1 <;>
    norm_num

/-- The Mellin integrand attached to one visible Type-II rectangle. -/
noncomputable def typeIIMellinRectangleIntegrand {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * Chen.lemma6SmoothingMellinKernel (x : ℝ) s *
    typeIISpectralRectangle U M N K L s χ

/-- Exact finite Mellin separation on a rectangle.  No integral or limiting
argument is involved here: this is the algebraic identity that will be put
under the already integrable smoothing kernel. -/
theorem sum_typeII_mellin_summands_eq_rectangleIntegrand {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (∑ l ∈ Finset.Ioc M (M + N),
      ∑ m ∈ Finset.Ioc K (K + L),
        (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (((x : ℝ) / ((l : ℝ) * m) : ℝ) : ℂ) ^ s *
              Chen.lemma6SmoothingMellinKernel (x : ℝ) s) =
      typeIIMellinRectangleIntegrand x U M N K L χ s := by
  rw [typeIIMellinRectangleIntegrand,
    typeIISpectralRectangle_eq_bilinear, bilinearCharacterRectangle]
  simp_rw [typeII_nat_quotient_cpow_factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul]
  unfold typeIISpectralLeft typeIISpectralLambda
  ring

/-- The complete Mellin rectangle integrand is integrable on Chen's
`alpha`-line.  This packages the termwise Cauchy-tail argument so finite
character sums may subsequently be interchanged with the vertical integral. -/
theorem integrable_typeIIMellinRectangleIntegrand_alpha {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ)) :
    MeasureTheory.Integrable (fun ν : ℝ =>
      typeIIMellinRectangleIntegrand x U M N K L χ
        (Chen.lemma6AlphaPoint x ν)) := by
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have ha : 0 < Chen.lemma6SmoothingScale (x : ℝ) := by
    unfold Chen.lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlogpos _
  have hn : 1 ≤ Chen.lemma6SmoothingOrder (x : ℝ) := by
    unfold Chen.lemma6SmoothingOrder
    exact Nat.le_floor (by simpa using hxlog)
  have hσ : 0 < 1 + 1 / Real.log (x : ℝ) := by positivity
  have hsummand (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      MeasureTheory.Integrable (fun ν : ℝ =>
        (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (((x : ℝ) / ((l : ℝ) * m) : ℝ) : ℂ) ^
                Chen.lemma6AlphaPoint x ν *
              Chen.lemma6SmoothingMellinKernel (x : ℝ)
                (Chen.lemma6AlphaPoint x ν)) := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hy : 0 < (x : ℝ) / ((l : ℝ) * m) := by positivity
    have hbase := Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
      hy ha hn hσ
    simpa only [Chen.lemma6AlphaPoint, mul_assoc] using
      hbase.const_mul
        ((vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))
  have hsum : MeasureTheory.Integrable (fun ν : ℝ =>
      ∑ l ∈ Finset.Ioc M (M + N),
        ∑ m ∈ Finset.Ioc K (K + L),
          (vaughanTypeIILeftCoefficient U l : ℂ) *
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
              (((x : ℝ) / ((l : ℝ) * m) : ℝ) : ℂ) ^
                  Chen.lemma6AlphaPoint x ν *
                Chen.lemma6SmoothingMellinKernel (x : ℝ)
                  (Chen.lemma6AlphaPoint x ν)) := by
    apply MeasureTheory.integrable_finsetSum
    intro l hl
    apply MeasureTheory.integrable_finsetSum
    intro m hm
    exact hsummand l hl m hm
  apply hsum.congr
  filter_upwards with ν
  exact sum_typeII_mellin_summands_eq_rectangleIntegrand
    x U M N K L χ (Chen.lemma6AlphaPoint x ν)

/-- One Type-II rectangle with Chen's smooth cutoff applied to the product
`l*m`. -/
noncomputable def smoothedTypeIIRectangle {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ l ∈ Finset.Ioc M (M + N),
    ∑ m ∈ Finset.Ioc K (K + L),
      (vaughanTypeIILeftCoefficient U l : ℂ) *
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
          (Chen.chenPhi (x : ℝ)
            ((x : ℝ) / ((l : ℝ) * m)) : ℂ)

/-- Mellin inversion and finite-sum interchange for a smoothed Type-II
rectangle.  All interchanges are finite; integrability comes from the
rational smoothing kernel's Cauchy tail. -/
theorem smoothedTypeIIRectangle_eq_verticalIntegral {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ)) :
    smoothedTypeIIRectangle x U M N K L χ =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          typeIIMellinRectangleIntegrand x U M N K L χ
            (Chen.lemma6AlphaPoint x ν) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℕ → ℕ → ℝ → ℂ := fun l m ν =>
    ((vaughanTypeIILeftCoefficient U l : ℂ) *
      (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m)) *
        ((((x : ℝ) / ((l : ℝ) * m) : ℝ) : ℂ) ^
            Chen.lemma6AlphaPoint x ν *
          Chen.lemma6SmoothingMellinKernel (x : ℝ)
            (Chen.lemma6AlphaPoint x ν))
  have hxreal : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have ha : 0 < Chen.lemma6SmoothingScale (x : ℝ) := by
    unfold Chen.lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlogpos _
  have hn : 1 ≤ Chen.lemma6SmoothingOrder (x : ℝ) := by
    unfold Chen.lemma6SmoothingOrder
    exact Nat.le_floor (by simpa using hxlog)
  have hσ : 0 < σ := by
    dsimp only [σ]
    positivity
  have hpoint (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (Chen.chenPhi (x : ℝ)
              ((x : ℝ) / ((l : ℝ) * m)) : ℂ) =
        (1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, F l m ν := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hy : 0 < (x : ℝ) / ((l : ℝ) * m) := by positivity
    have hphi := Chen.chenPhi_eq_smoothing_verticalIntegral
      hxreal ha hn hσ hy
    change (Chen.chenPhi (x : ℝ) ((x : ℝ) / ((l : ℝ) * m)) : ℂ) = _ at hphi
    simp only [σ] at hphi
    rw [hphi]
    rw [MeasureTheory.integral_const_mul]
    simp only [Complex.real_smul, Chen.lemma6AlphaPoint]
    ring
  have hFint (l : ℕ) (hl : l ∈ Finset.Ioc M (M + N))
      (m : ℕ) (hm : m ∈ Finset.Ioc K (K + L)) :
      MeasureTheory.Integrable (F l m) := by
    have hlpos : 0 < l := by
      have := (Finset.mem_Ioc.mp hl).1
      omega
    have hmpos : 0 < m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hy : 0 < (x : ℝ) / ((l : ℝ) * m) := by positivity
    have hbase := Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
      hy ha hn hσ
    simpa only [F, σ, Chen.lemma6AlphaPoint] using
      hbase.const_mul
        ((vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m))
  rw [smoothedTypeIIRectangle]
  calc
    (∑ l ∈ Finset.Ioc M (M + N),
      ∑ m ∈ Finset.Ioc K (K + L),
        (vaughanTypeIILeftCoefficient U l : ℂ) *
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (l * m) *
            (Chen.chenPhi (x : ℝ)
              ((x : ℝ) / ((l : ℝ) * m)) : ℂ)) =
        ∑ l ∈ Finset.Ioc M (M + N),
          ∑ m ∈ Finset.Ioc K (K + L),
            (1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, F l m ν := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro m hm
      exact hpoint l hl m hm
    _ = (1 / (2 * Real.pi) : ℝ) •
          ∑ l ∈ Finset.Ioc M (M + N),
            ∑ m ∈ Finset.Ioc K (K + L), ∫ ν : ℝ, F l m ν := by
      simp only [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
          ∫ ν : ℝ,
            ∑ l ∈ Finset.Ioc M (M + N),
              ∑ m ∈ Finset.Ioc K (K + L), F l m ν := by
      congr 1
      rw [MeasureTheory.integral_finsetSum (Finset.Ioc M (M + N))]
      · apply Finset.sum_congr rfl
        intro l hl
        exact (MeasureTheory.integral_finsetSum
          (Finset.Ioc K (K + L)) (hFint l hl)).symm
      · intro l hl
        exact MeasureTheory.integrable_finsetSum
          (Finset.Ioc K (K + L)) (hFint l hl)
    _ = (1 / (2 * Real.pi) : ℝ) •
          ∫ ν : ℝ,
            typeIIMellinRectangleIntegrand x U M N K L χ
              (Chen.lemma6AlphaPoint x ν) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ν
      dsimp only [F]
      simpa only [mul_assoc] using
        sum_typeII_mellin_summands_eq_rectangleIntegrand
          x U M N K L χ (Chen.lemma6AlphaPoint x ν)

/-- Taking norms in the Mellin representation leaves a scalar integral
majorant.  This is the form in which the character large sieve is applied
at each height. -/
theorem norm_smoothedTypeIIRectangle_le_integral {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ)) :
    ‖smoothedTypeIIRectangle x U M N K L χ‖ ≤
      (1 / (2 * Real.pi)) *
        ∫ ν : ℝ,
          ‖typeIIMellinRectangleIntegrand x U M N K L χ
            (Chen.lemma6AlphaPoint x ν)‖ := by
  rw [smoothedTypeIIRectangle_eq_verticalIntegral
    x U M N K L χ hx hxlog, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  gcongr
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- On Chen's original Mellin line, the `x^s` factor has the constant
modulus `e*x`; all height dependence is confined to the smoothing kernel
and the two separated Dirichlet polynomials. -/
theorem norm_typeIIMellinRectangleIntegrand_alpha {q : ℕ}
    (x U M N K L : ℕ) (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (ν : ℝ) :
    ‖typeIIMellinRectangleIntegrand x U M N K L χ
        (Chen.lemma6AlphaPoint x ν)‖ =
      (Real.exp 1 * (x : ℝ)) *
        ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
          (Chen.lemma6AlphaPoint x ν)‖ *
        ‖characterIntervalSum M N
          (typeIISpectralLeft U (Chen.lemma6AlphaPoint x ν)) χ‖ *
        ‖characterIntervalSum K L
          (typeIISpectralLambda (Chen.lemma6AlphaPoint x ν)) χ‖ := by
  rw [typeIIMellinRectangleIntegrand, typeIISpectralRectangle]
  simp only [norm_mul, Chen.norm_nat_cpow_lemma6AlphaPoint hx ν]
  ring

/-- Pointwise in the Mellin height, the squared primitive-character mean of
the complete rectangle integrand is bounded by the kernel modulus squared
times the height-independent spectral large-sieve majorant. -/
theorem typeIIMellinRectangleIntegrandMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ) (ν : ℝ),
        2 ≤ x → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖typeIIMellinRectangleIntegrand x U M N K L i.2
                  (Chen.lemma6AlphaPoint x ν)‖) ^ 2 ≤
            ((Real.exp 1 * (x : ℝ)) *
                ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
                  (Chen.lemma6AlphaPoint x ν)‖) ^ 2 *
              typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L := by
  rcases typeIISpectralRectangleMean_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hspectral⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L ν hx hD hDQ hM hK hMN hKL
  let W : ℝ := (Real.exp 1 * (x : ℝ)) *
    ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
      (Chen.lemma6AlphaPoint x ν)‖
  have hs : 1 ≤ (Chen.lemma6AlphaPoint x ν).re :=
    (Chen.one_lt_lemma6AlphaPoint_re hx ν).le
  have hspec := hspectral U D Q M N K L
    (Chen.lemma6AlphaPoint x ν) hs hD hDQ hM hK hMN hKL
  have hsum :
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖typeIIMellinRectangleIntegrand x U M N K L i.2
              (Chen.lemma6AlphaPoint x ν)‖) =
        W * ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖typeIISpectralRectangle U M N K L
              (Chen.lemma6AlphaPoint x ν) i.2‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_typeIIMellinRectangleIntegrand_alpha
      x U M N K L i.2 hx ν]
    rw [typeIISpectralRectangle, norm_mul]
    dsimp only [W]
    ring
  rw [hsum]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hspec (sq_nonneg W)

/-- Unsquared pointwise mean bound, obtained from the preceding square
estimate.  This is the exact form needed under the Mellin integral. -/
theorem typeIIMellinRectangleIntegrandMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ) (ν : ℝ),
        2 ≤ x → 1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖typeIIMellinRectangleIntegrand x U M N K L i.2
                  (Chen.lemma6AlphaPoint x ν)‖) ≤
            (Real.exp 1 * (x : ℝ)) *
                ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
                  (Chen.lemma6AlphaPoint x ν)‖ *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) := by
  rcases typeIIMellinRectangleIntegrandMean_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hsquare⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L ν hx hD hDQ hM hK hMN hKL
  let S : ℝ := ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i *
      ‖typeIIMellinRectangleIntegrand x U M N K L i.2
        (Chen.lemma6AlphaPoint x ν)‖
  let W : ℝ := (Real.exp 1 * (x : ℝ)) *
    ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
      (Chen.lemma6AlphaPoint x ν)‖
  let R : ℝ := typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact typeIISpectralRectangleMajorant_nonneg
      hC₀.le hC₁.le hD hM hK hMN hKL
  have hsq : S ^ 2 ≤ W ^ 2 * R := by
    simpa only [S, W, R] using
      hsquare x U D Q M N K L ν hx hD hDQ hM hK hMN hKL
  apply (sq_le_sq₀ hS (mul_nonneg hW (Real.sqrt_nonneg R))).1
  rw [mul_pow, Real.sq_sqrt hR]
  exact hsq

/-- The primitive-character mean of one smoothed Type-II rectangle is
bounded by the integral of the scalar smoothing kernel times the spectral
large-sieve majorant.  Every exchange here is finite and justified by the
integrability theorem above. -/
theorem smoothedTypeIIRectangleMean_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ),
        2 ≤ x → 1 ≤ Real.log (x : ℝ) →
          1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖smoothedTypeIIRectangle x U M N K L i.2‖) ≤
            (1 / (2 * Real.pi)) * (Real.exp 1 * (x : ℝ)) *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
              ∫ ν : ℝ,
                ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
                  (Chen.lemma6AlphaPoint x ν)‖ := by
  rcases typeIIMellinRectangleIntegrandMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hpoint⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L hx hxlog hD hDQ hM hK hMN hKL
  let I := characterIndicesIoc D Q
  let G : (i : (q : ℕ) × DirichletCharacter ℂ q) → ℝ → ℝ := fun i ν =>
    primitiveDyadicWeight i *
      ‖typeIIMellinRectangleIntegrand x U M N K L i.2
        (Chen.lemma6AlphaPoint x ν)‖
  let H : ℝ → ℝ := fun ν =>
    (Real.exp 1 * (x : ℝ)) *
      ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
        (Chen.lemma6AlphaPoint x ν)‖ *
      Real.sqrt
        (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L)
  have hGint (i : (q : ℕ) × DirichletCharacter ℂ q) (hi : i ∈ I) :
      MeasureTheory.Integrable (G i) := by
    dsimp only [G]
    exact (integrable_typeIIMellinRectangleIntegrand_alpha
      x U M N K L i.2 hx hxlog).norm.const_mul (primitiveDyadicWeight i)
  have hsumInt : MeasureTheory.Integrable (fun ν : ℝ =>
      ∑ i ∈ I, G i ν) :=
    MeasureTheory.integrable_finsetSum I hGint
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have ha : 0 < Chen.lemma6SmoothingScale (x : ℝ) := by
    unfold Chen.lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlogpos _
  have hn : 1 ≤ Chen.lemma6SmoothingOrder (x : ℝ) := by
    unfold Chen.lemma6SmoothingOrder
    exact Nat.le_floor (by simpa using hxlog)
  have hσ : 0 < 1 + 1 / Real.log (x : ℝ) := by positivity
  have hk := Chen.verticalIntegrable_lemma6SmoothingMellinKernel ha hn hσ
  rw [Complex.VerticalIntegrable] at hk
  have hkNorm : MeasureTheory.Integrable (fun ν : ℝ =>
      ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
        (Chen.lemma6AlphaPoint x ν)‖) := by
    simpa only [Chen.lemma6AlphaPoint] using hk.norm
  have hHint : MeasureTheory.Integrable H := by
    have hscaled := hkNorm.const_mul
      ((Real.exp 1 * (x : ℝ)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L))
    apply hscaled.congr
    filter_upwards with ν
    dsimp only [H]
    ring
  have hmeanIntegral :
      (∫ ν : ℝ, ∑ i ∈ I, G i ν) ≤ ∫ ν : ℝ, H ν := by
    apply MeasureTheory.integral_mono hsumInt hHint
    intro ν
    simpa only [I, G, H] using
      hpoint x U D Q M N K L ν hx hD hDQ hM hK hMN hKL
  have hsumIntegral :
      (∑ i ∈ I, primitiveDyadicWeight i *
          ∫ ν : ℝ,
            ‖typeIIMellinRectangleIntegrand x U M N K L i.2
              (Chen.lemma6AlphaPoint x ν)‖) =
        ∫ ν : ℝ, ∑ i ∈ I, G i ν := by
    rw [MeasureTheory.integral_finsetSum I hGint]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [MeasureTheory.integral_const_mul]
  have hHIntegral :
      (∫ ν : ℝ, H ν) =
        ((Real.exp 1 * (x : ℝ)) *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L)) *
          ∫ ν : ℝ,
            ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
              (Chen.lemma6AlphaPoint x ν)‖ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ν
    dsimp only [H]
    ring
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖smoothedTypeIIRectangle x U M N K L i.2‖) ≤
        ∑ i ∈ I, primitiveDyadicWeight i *
          ((1 / (2 * Real.pi)) *
            ∫ ν : ℝ,
              ‖typeIIMellinRectangleIntegrand x U M N K L i.2
                (Chen.lemma6AlphaPoint x ν)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact norm_smoothedTypeIIRectangle_le_integral
          x U M N K L i.2 hx hxlog
      · exact primitiveDyadicWeight_nonneg i
    _ = (1 / (2 * Real.pi)) *
          ∑ i ∈ I, primitiveDyadicWeight i *
            ∫ ν : ℝ,
              ‖typeIIMellinRectangleIntegrand x U M N K L i.2
                (Chen.lemma6AlphaPoint x ν)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (1 / (2 * Real.pi)) *
          ∫ ν : ℝ, ∑ i ∈ I, G i ν := by rw [hsumIntegral]
    _ ≤ (1 / (2 * Real.pi)) * ∫ ν : ℝ, H ν := by
      exact mul_le_mul_of_nonneg_left hmeanIntegral (by positivity)
    _ = (1 / (2 * Real.pi)) * (Real.exp 1 * (x : ℝ)) *
          Real.sqrt
            (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
          ∫ ν : ℝ,
            ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
              (Chen.lemma6AlphaPoint x ν)‖ := by
      rw [hHIntegral]
      ring

/-- The unweighted scalar kernel mass is controlled by the quadratic-mass
bound already established in the Lemma 6 contour analysis. -/
theorem integral_norm_lemma6SmoothingMellinKernel_alpha_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    (∫ ν : ℝ,
        ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
          (Chen.lemma6AlphaPoint x ν)‖) ≤
      2 * Real.pi * Real.log (x : ℝ) ^ 5 := by
  have hweighted := Chen.integrable_kernelNorm_alpha_mul_one_add_sq hxlog
  have hplain : MeasureTheory.Integrable (fun ν : ℝ =>
      ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
        (Chen.lemma6AlphaPoint x ν)‖) := by
    apply hweighted.mono' (Chen.aestronglyMeasurable_norm_kernel_alpha hxlog)
    filter_upwards with ν
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    nlinarith [norm_nonneg
      (Chen.lemma6SmoothingMellinKernel (x : ℝ)
        (Chen.lemma6AlphaPoint x ν)), sq_nonneg ν]
  calc
    (∫ ν : ℝ,
        ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
          (Chen.lemma6AlphaPoint x ν)‖) ≤
        ∫ ν : ℝ,
          ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
            (Chen.lemma6AlphaPoint x ν)‖ * (1 + ν ^ 2) := by
      apply MeasureTheory.integral_mono hplain hweighted
      intro ν
      nlinarith [norm_nonneg
        (Chen.lemma6SmoothingMellinKernel (x : ℝ)
          (Chen.lemma6AlphaPoint x ν)), sq_nonneg ν]
    _ ≤ 2 * Real.pi * Real.log (x : ℝ) ^ 5 :=
      Chen.integral_kernelNorm_alpha_mul_one_add_sq_le hxlog

/-- Explicit logarithmic form of the smoothed Type-II rectangle estimate;
the factors `1/(2π)` and `2π` from Mellin inversion and kernel mass cancel. -/
theorem smoothedTypeIIRectangleMean_le_log_five :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U D Q M N K L : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ D → D ≤ Q → 1 ≤ M → 1 ≤ K →
          2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖smoothedTypeIIRectangle x U M N K L i.2‖) ≤
            (Real.exp 1 * (x : ℝ)) *
              Real.sqrt
                (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
              Real.log (x : ℝ) ^ 5 := by
  rcases smoothedTypeIIRectangleMean_le with
    ⟨C₀, C₁, hC₀, hC₁, hrectangle⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U D Q M N K L hx hxlog hD hDQ hM hK hMN hKL
  apply (hrectangle x U D Q M N K L hx (by linarith)
    hD hDQ hM hK hMN hKL).trans
  have hkernel := integral_norm_lemma6SmoothingMellinKernel_alpha_le hxlog
  have hfactor : 0 ≤
      (1 / (2 * Real.pi)) * (Real.exp 1 * (x : ℝ)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) := by
    positivity
  calc
    (1 / (2 * Real.pi)) * (Real.exp 1 * (x : ℝ)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
        ∫ ν : ℝ,
          ‖Chen.lemma6SmoothingMellinKernel (x : ℝ)
            (Chen.lemma6AlphaPoint x ν)‖ ≤
      ((1 / (2 * Real.pi)) * (Real.exp 1 * (x : ℝ)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L)) *
        (2 * Real.pi * Real.log (x : ℝ) ^ 5) := by
      exact mul_le_mul_of_nonneg_left hkernel hfactor
    _ = (Real.exp 1 * (x : ℝ)) *
        Real.sqrt
          (typeIISpectralRectangleMajorant C₀ C₁ D Q M N K L) *
        Real.log (x : ℝ) ^ 5 := by
      field_simp [Real.pi_ne_zero]

end Chen.BombieriVinogradov
