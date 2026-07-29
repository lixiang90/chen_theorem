import ChenTheorem.Lemma5.Boundary.Selberg

/-!
# Optimal truncated Selberg weights for Chen's Lemma 5

This file performs Möbius inversion on the upper divisor lattice of the
squarefree sieve product.  It constructs weights whose diagonal
coordinates are the standard optimal Selberg coordinates.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

theorem div_div_self_of_dvd {P n : ℕ} (hP : 0 < P) (hn : n ∣ P) :
    P / (P / n) = n := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn hP
  have hquotpos : 0 < P / n :=
    Nat.div_pos (Nat.le_of_dvd hP hn) hnpos
  apply Nat.div_eq_of_eq_mul_left hquotpos
  exact (Nat.mul_div_cancel' hn).symm

/-- Möbius inversion coefficient on the upper divisor interval
`{d | d ∣ P}`. -/
noncomputable def upperMobiusCoefficient
    (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ uv ∈ (P / d).divisorsAntidiagonal,
    (ArithmeticFunction.moebius uv.1 : ℝ) * y (P / uv.2)

/-- Upper-divisor Möbius inversion. -/
theorem upperMobiusCoefficient_sum
    {P k : ℕ} (y : ℕ → ℝ) (hP : 0 < P) (hk : k ∣ P) :
    (∑ d ∈ P.divisors,
      if k ∣ d then upperMobiusCoefficient P y d else 0) = y k := by
  have hinv :
      ∀ n > 0, n ∣ P →
        (∑ i ∈ n.divisors,
          upperMobiusCoefficient P y (P / i)) = y (P / n) := by
    apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      {n : ℕ | n ∣ P} (by
        intro m n hmn hnP
        exact hmn.trans hnP)).mpr
    intro n hnpos hnP
    rw [upperMobiusCoefficient, div_div_self_of_dvd hP hnP]
  rw [← Nat.sum_div_divisors P]
  have hcond :
      ∀ i ∈ P.divisors, (k ∣ P / i ↔ i ∣ P / k) := by
    intro i hi
    have hiP := Nat.dvd_of_mem_divisors hi
    rw [Nat.dvd_div_iff_mul_dvd hiP,
      Nat.dvd_div_iff_mul_dvd hk]
    exact mul_comm k i ▸ Iff.rfl
  calc
    (∑ i ∈ P.divisors,
        if k ∣ P / i then
          upperMobiusCoefficient P y (P / i) else 0) =
        ∑ i ∈ P.divisors,
          if i ∣ P / k then
            upperMobiusCoefficient P y (P / i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [hcond i hi]
    _ = ∑ i ∈ (P / k).divisors,
          upperMobiusCoefficient P y (P / i) := by
      rw [← Nat.divisors_filter_dvd_of_dvd hP.ne'
          (Nat.div_dvd_of_dvd hk),
        Finset.sum_filter]
    _ = y (P / (P / k)) := by
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk hP
      have hquotpos : 0 < P / k :=
        Nat.div_pos (Nat.le_of_dvd hP hk) hkpos
      exact hinv (P / k) hquotpos (Nat.div_dvd_of_dvd hk)
    _ = y k := by rw [div_div_self_of_dvd hP hk]

/-- If all coordinates above `d` vanish, then so does its inverse
coefficient. -/
theorem upperMobiusCoefficient_eq_zero
    {P d : ℕ} (y : ℕ → ℝ) (hP : 0 < P) (hdP : d ∣ P)
    (hy : ∀ l, 0 < l → d ∣ l → y l = 0) :
    upperMobiusCoefficient P y d = 0 := by
  unfold upperMobiusCoefficient
  apply Finset.sum_eq_zero
  intro uv huv
  have huv' := (Nat.mem_divisorsAntidiagonal.mp huv).1
  have hdprod : d * (P / d) = P := Nat.mul_div_cancel' hdP
  have hvpos : 0 < uv.2 :=
    Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal huv)
  have hquot :
      P / uv.2 = d * uv.1 := by
    apply Nat.div_eq_of_eq_mul_right hvpos
    calc
      P = d * (P / d) := hdprod.symm
      _ = d * (uv.1 * uv.2) := by rw [huv']
      _ = (d * uv.1) * uv.2 := by ring
      _ = uv.2 * (d * uv.1) := by ring
  have hvP : uv.2 ∣ P := by
    exact (dvd_of_mul_left_dvd huv'.dvd).trans
      (Nat.div_dvd_of_dvd hdP)
  have hlpos : 0 < P / uv.2 :=
    Nat.div_pos (Nat.le_of_dvd hP hvP) hvpos
  rw [hy (P / uv.2) hlpos ⟨uv.1, hquot⟩, mul_zero]

/-- The desired diagonal coordinates of the optimal truncated Selberg
weight. -/
noncomputable def optimalSelbergCoordinate
    (s : BoundingSieve) (R : ℕ) (l : ℕ) : ℝ :=
  if l ∈ truncatedSieveDivisors s.prodPrimes R then
    (ArithmeticFunction.moebius l : ℝ) *
      s.selbergTerms l / truncatedSelbergMass s R
  else 0

/-- The optimal truncated Selberg weight, obtained from the desired
coordinates by upper-divisor Möbius inversion. -/
noncomputable def optimalSelbergWeight
    (s : BoundingSieve) (R : ℕ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ *
      upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d
  else 0

theorem optimalSelbergCoordinate_eq_zero_of_not_le
    (s : BoundingSieve) {R l : ℕ} (hlR : ¬l ≤ R) :
    optimalSelbergCoordinate s R l = 0 := by
  simp [optimalSelbergCoordinate, truncatedSieveDivisors, hlR]

theorem optimalSelbergCoordinate_abs_le_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) (l : ℕ) :
    |optimalSelbergCoordinate s R l| ≤ 1 := by
  by_cases hlD :
      l ∈ truncatedSieveDivisors s.prodPrimes R
  · have hlP :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hlD).1
    have hlsq : Squarefree l :=
      s.squarefree_of_dvd_prodPrimes hlP
    have hmu :
        |(ArithmeticFunction.moebius l : ℝ)| = 1 := by
      exact_mod_cast
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hlsq
    have hgpos : 0 < s.selbergTerms l :=
      s.selbergTerms_pos hlP
    have hGpos := truncatedSelbergMass_pos s hR
    have hleG :
        s.selbergTerms l ≤ truncatedSelbergMass s R := by
      unfold truncatedSelbergMass
      exact Finset.single_le_sum
        (fun i hi => (s.selbergTerms_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hi).1)).le)
        hlD
    rw [optimalSelbergCoordinate, if_pos hlD,
      abs_div, abs_mul, hmu, one_mul,
      abs_of_pos hgpos, abs_of_pos hGpos]
    exact (div_le_one hGpos).2 hleG
  · simp [optimalSelbergCoordinate, hlD]

/-- The inverse Möbius coefficient is bounded by the number of possible
nonzero level-`R` coordinates. -/
theorem abs_upperMobiusCoefficient_optimal_le
    (s : BoundingSieve) {R d : ℕ} (hR : 1 ≤ R)
    (hdP : d ∣ s.prodPrimes) :
    |upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d| ≤ R + 1 := by
  let A := (s.prodPrimes / d).divisorsAntidiagonal
  let T := A.filter fun uv => s.prodPrimes / uv.2 ≤ R
  have hPpos : 0 < s.prodPrimes :=
    Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  have hTcard : T.card ≤ R + 1 := by
    have hmap :
        Set.MapsTo (fun uv : ℕ × ℕ => s.prodPrimes / uv.2)
          (T : Set (ℕ × ℕ)) (Finset.range (R + 1) : Set ℕ) := by
      intro uv huv
      change s.prodPrimes / uv.2 ∈ Finset.range (R + 1)
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_filter.mp huv).2
    have hinj :
        Set.InjOn (fun uv : ℕ × ℕ => s.prodPrimes / uv.2)
          (T : Set (ℕ × ℕ)) := by
      intro u hu v hv huvEq
      have huA := (Nat.mem_divisorsAntidiagonal.mp
        (Finset.mem_filter.mp hu).1)
      have hvA := (Nat.mem_divisorsAntidiagonal.mp
        (Finset.mem_filter.mp hv).1)
      have hu2dvdQ : u.2 ∣ s.prodPrimes / d :=
        ⟨u.1, by simpa [mul_comm] using huA.1.symm⟩
      have hv2dvdQ : v.2 ∣ s.prodPrimes / d :=
        ⟨v.1, by simpa [mul_comm] using hvA.1.symm⟩
      have hu2P : u.2 ∣ s.prodPrimes :=
        hu2dvdQ.trans (Nat.div_dvd_of_dvd hdP)
      have hv2P : v.2 ∣ s.prodPrimes :=
        hv2dvdQ.trans (Nat.div_dvd_of_dvd hdP)
      have huv2 : u.2 = v.2 :=
        (Nat.div_eq_iff_eq_of_dvd_dvd
          s.prodPrimes_ne_zero hu2P hv2P).mp huvEq
      apply Prod.ext
      · have hu2pos : 0 < u.2 :=
          Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal
              (Finset.mem_filter.mp hu).1)
        apply Nat.mul_right_cancel hu2pos
        calc
          u.1 * u.2 = s.prodPrimes / d := huA.1
          _ = v.1 * v.2 := hvA.1.symm
          _ = v.1 * u.2 := by rw [huv2]
      · exact huv2
    simpa using Finset.card_le_card_of_injOn
      (fun uv : ℕ × ℕ => s.prodPrimes / uv.2) hmap hinj
  unfold upperMobiusCoefficient
  change |∑ uv ∈ A,
      (ArithmeticFunction.moebius uv.1 : ℝ) *
        optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| ≤
    (R : ℝ) + 1
  calc
    |∑ uv ∈ A,
        (ArithmeticFunction.moebius uv.1 : ℝ) *
          optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| ≤
        ∑ uv ∈ A,
          |(ArithmeticFunction.moebius uv.1 : ℝ) *
            optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ uv ∈ A,
          if s.prodPrimes / uv.2 ≤ R then 1 else 0 := by
      apply Finset.sum_le_sum
      intro uv huv
      by_cases huvR : s.prodPrimes / uv.2 ≤ R
      · rw [if_pos huvR, abs_mul]
        have hmu :
            |(ArithmeticFunction.moebius uv.1 : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [optimalSelbergCoordinate_abs_le_one s hR
          (s.prodPrimes / uv.2),
          abs_nonneg (ArithmeticFunction.moebius uv.1 : ℝ),
          abs_nonneg (optimalSelbergCoordinate s R
            (s.prodPrimes / uv.2))]
      · rw [if_neg huvR,
          optimalSelbergCoordinate_eq_zero_of_not_le s huvR,
          mul_zero, abs_zero]
    _ = T.card := by
      simp [T, A]
    _ ≤ R + 1 := by exact_mod_cast hTcard

theorem smoothingTransitionRootCount_pos
    (x : ℕ) (q : ℕ × ℕ) {d : ℕ} (hd : 0 < d) :
    0 < smoothingTransitionRootCount x q d := by
  unfold smoothingTransitionRootCount
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [smoothingTransitionRootResidues, hd]

theorem smoothingTransitionNu_inv_le
    (x : ℕ) (q : ℕ × ℕ) {d : ℕ} (hd : 0 < d) :
    (smoothingTransitionNu x q d)⁻¹ ≤ (d : ℝ) := by
  rw [smoothingTransitionNu_apply, inv_div]
  have hrpos :
      0 < smoothingTransitionRootCount x q d :=
    smoothingTransitionRootCount_pos x q hd
  rw [div_le_iff₀ (Nat.cast_pos.2 hrpos)]
  have hrone :
      (1 : ℝ) ≤ smoothingTransitionRootCount x q d := by
    exact_mod_cast hrpos
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  nlinarith

/-- A polynomial bound for the optimal transition weights.  The exact
classical bound is `|λ_d| ≤ 1`; this weaker bound already makes the
indexed congruence error negligible after choosing a sufficiently small
power level. -/
theorem abs_optimalTransitionSelbergWeight_le
    {x R d : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R)
    (hd : d ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    |optimalSelbergWeight s R d| ≤
      (R : ℝ) * ((R : ℝ) + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  change |optimalSelbergWeight s R d| ≤
    (R : ℝ) * ((R : ℝ) + 1)
  have hdP : d ∣ transitionSieveProduct x :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdR : d ≤ R := (Finset.mem_filter.mp hd).2
  have hdPs : d ∣ s.prodPrimes := by exact hdP
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdP
      (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
  have hcoeff :=
    abs_upperMobiusCoefficient_optimal_le s hR hdP
  have hnuinv :=
    smoothingTransitionNu_inv_le x q hdpos
  have hnupos :
      0 < s.nu d :=
    s.nu_pos_of_dvd_prodPrimes hdPs
  rw [optimalSelbergWeight, if_pos hdPs, abs_mul,
    abs_inv, abs_of_pos hnupos]
  have hdRreal : (d : ℝ) ≤ R := by exact_mod_cast hdR
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hcoeffnonneg :
      0 ≤ |upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d| := abs_nonneg _
  calc
    (s.nu d)⁻¹ *
        |upperMobiusCoefficient s.prodPrimes
          (optimalSelbergCoordinate s R) d| ≤
        (d : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul hnuinv hcoeff
        (by positivity) (by positivity)
    _ ≤ (R : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right hdRreal (by positivity)

/-- The congruence-count error for the optimal weights remains
polynomial in the chosen level. -/
theorem transitionErrorQuadratic_optimalSelbergWeight_le
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    transitionErrorQuadratic x q R (optimalSelbergWeight s R) ≤
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  let K : ℝ := (R : ℝ) * ((R : ℝ) + 1)
  let w := optimalSelbergWeight s R
  let wn : ℕ → ℝ := fun d => w d / K
  have hKpos : 0 < K := by
    dsimp only [K]
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have hwn :
      ∀ d ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R, |wn d| ≤ 1 := by
    intro d hd
    have hw := abs_optimalTransitionSelbergWeight_le
      hx hxEven hq hR hd
    change |w d / K| ≤ 1
    rw [abs_div, abs_of_pos hKpos]
    exact (div_le_one hKpos).2 (by
      simpa only [w, K, s] using hw)
  have herr :=
    transitionErrorQuadratic_le x q R wn hwn
  have herrEq :
      transitionErrorQuadratic x q R w =
        K ^ 2 * transitionErrorQuadratic x q R wn := by
    unfold transitionErrorQuadratic
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    dsimp only [wn]
    simp only [abs_mul, abs_div, abs_of_pos hKpos]
    field_simp
  change transitionErrorQuadratic x q R w ≤
    K ^ 2 * ((R + 1 : ℕ) : ℝ) ^ 2 *
      (3 * (R : ℝ) ^ 2 + 1)
  rw [herrEq]
  nlinarith [sq_nonneg K]

/-- The inverse weight is supported at level `R`. -/
theorem optimalSelbergWeight_eq_zero_of_not_le
    (s : BoundingSieve) {R d : ℕ} (hdR : ¬d ≤ R) :
    optimalSelbergWeight s R d = 0 := by
  by_cases hdP : d ∣ s.prodPrimes
  · rw [optimalSelbergWeight, if_pos hdP,
      upperMobiusCoefficient_eq_zero _
        (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hdP]
    · simp
    · intro l hlpos hdl
      apply optimalSelbergCoordinate_eq_zero_of_not_le
      exact fun hlR => hdR (Nat.le_trans
        (Nat.le_of_dvd hlpos hdl) hlR)
  · simp [optimalSelbergWeight, hdP]

@[simp]
theorem smoothingTruncatedWeight_optimalSelbergWeight
    (s : BoundingSieve) (R d : ℕ) :
    smoothingTruncatedWeight R (optimalSelbergWeight s R) d =
      optimalSelbergWeight s R d := by
  by_cases hdR : d ≤ R
  · exact smoothingTruncatedWeight_of_le hdR
  · rw [smoothingTruncatedWeight_of_not_le hdR,
      optimalSelbergWeight_eq_zero_of_not_le s hdR]

/-- The constructed weight has exactly the prescribed diagonal
coordinates. -/
theorem optimalSelbergWeight_coordinate
    (s : BoundingSieve) (R : ℕ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalSelbergWeight s R d else 0) =
      optimalSelbergCoordinate s R l := by
  calc
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * optimalSelbergWeight s R d else 0) =
        ∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            upperMobiusCoefficient s.prodPrimes
              (optimalSelbergCoordinate s R) d
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hnu : s.nu d ≠ 0 :=
        ne_of_gt (s.nu_pos_of_dvd_prodPrimes hdP)
      by_cases hld : l ∣ d
      · simp only [hld, if_true, optimalSelbergWeight, hdP]
        field_simp
      · simp [hld]
    _ = optimalSelbergCoordinate s R l :=
      upperMobiusCoefficient_sum _ (Nat.pos_of_ne_zero
        s.prodPrimes_ne_zero) hl

/-- The diagonal quadratic form at the optimal coordinates is exactly
the reciprocal of the truncated Selberg mass. -/
theorem optimalSelbergCoordinate_diagonal
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    (∑ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (optimalSelbergCoordinate s R l) ^ 2) =
      (truncatedSelbergMass s R)⁻¹ := by
  have hGpos := truncatedSelbergMass_pos s hR
  calc
    (∑ l ∈ s.prodPrimes.divisors,
        (s.selbergTerms l)⁻¹ *
          (optimalSelbergCoordinate s R l) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors,
          if l ≤ R then
            s.selbergTerms l / (truncatedSelbergMass s R) ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hlR : l ≤ R
      · rw [if_pos hlR]
        have hlD :
            l ∈ truncatedSieveDivisors s.prodPrimes R :=
          Finset.mem_filter.mpr ⟨hl, hlR⟩
        have hlsq : Squarefree l :=
          s.squarefree_of_dvd_prodPrimes
            (Nat.dvd_of_mem_divisors hl)
        have hmu :
            ((ArithmeticFunction.moebius l : ℝ) ^ 2) = 1 := by
          exact_mod_cast
            ArithmeticFunction.moebius_sq_eq_one_of_squarefree hlsq
        have hgpos :
            0 < s.selbergTerms l :=
          s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
        rw [optimalSelbergCoordinate, if_pos hlD]
        field_simp
        nlinarith
      · rw [if_neg hlR]
        have hlD :
            l ∉ truncatedSieveDivisors s.prodPrimes R := by
          simp [truncatedSieveDivisors, hlR]
        simp [optimalSelbergCoordinate, hlD]
    _ = (∑ l ∈ truncatedSieveDivisors s.prodPrimes R,
          s.selbergTerms l) /
        (truncatedSelbergMass s R) ^ 2 := by
      rw [← Finset.sum_filter]
      simp only [truncatedSieveDivisors]
      rw [Finset.sum_div]
    _ = (truncatedSelbergMass s R) /
        (truncatedSelbergMass s R) ^ 2 := by
      rfl
    _ = (truncatedSelbergMass s R)⁻¹ := by
      field_simp

theorem upperMobiusCoefficient_optimal_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    upperMobiusCoefficient s.prodPrimes
      (optimalSelbergCoordinate s R) 1 = 1 := by
  have hPpos : 0 < s.prodPrimes :=
    Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  have hGpos := truncatedSelbergMass_pos s hR
  unfold upperMobiusCoefficient
  rw [Nat.div_one,
    Nat.sum_divisorsAntidiagonal
      (fun i j => (ArithmeticFunction.moebius i : ℝ) *
        optimalSelbergCoordinate s R (s.prodPrimes / j))]
  calc
    (∑ i ∈ s.prodPrimes.divisors,
        (ArithmeticFunction.moebius i : ℝ) *
          optimalSelbergCoordinate s R
            (s.prodPrimes / (s.prodPrimes / i))) =
        ∑ i ∈ s.prodPrimes.divisors,
          if i ≤ R then
            s.selbergTerms i / truncatedSelbergMass s R
          else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_div_self_of_dvd hPpos
        (Nat.dvd_of_mem_divisors hi)]
      by_cases hiR : i ≤ R
      · rw [if_pos hiR]
        have hiD :
            i ∈ truncatedSieveDivisors s.prodPrimes R :=
          Finset.mem_filter.mpr ⟨hi, hiR⟩
        have hisq : Squarefree i :=
          s.squarefree_of_dvd_prodPrimes
            (Nat.dvd_of_mem_divisors hi)
        have hmu :
            ((ArithmeticFunction.moebius i : ℝ) ^ 2) = 1 := by
          exact_mod_cast
            ArithmeticFunction.moebius_sq_eq_one_of_squarefree hisq
        rw [optimalSelbergCoordinate, if_pos hiD]
        calc
          (ArithmeticFunction.moebius i : ℝ) *
              ((ArithmeticFunction.moebius i : ℝ) *
                s.selbergTerms i / truncatedSelbergMass s R) =
              ((ArithmeticFunction.moebius i : ℝ) ^ 2) *
                s.selbergTerms i / truncatedSelbergMass s R := by ring
          _ = s.selbergTerms i / truncatedSelbergMass s R := by
            rw [hmu, one_mul]
      · rw [if_neg hiR]
        have hiD :
            i ∉ truncatedSieveDivisors s.prodPrimes R := by
          simp [truncatedSieveDivisors, hiR]
        simp [optimalSelbergCoordinate, hiD]
    _ = (∑ i ∈ truncatedSieveDivisors s.prodPrimes R,
          s.selbergTerms i) / truncatedSelbergMass s R := by
      rw [← Finset.sum_filter]
      simp only [truncatedSieveDivisors]
      rw [Finset.sum_div]
    _ = truncatedSelbergMass s R /
        truncatedSelbergMass s R := by rfl
    _ = 1 := div_self hGpos.ne'

@[simp]
theorem optimalSelbergWeight_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    optimalSelbergWeight s R 1 = 1 := by
  rw [optimalSelbergWeight, if_pos (one_dvd _),
    s.nu_mult.map_one, inv_one, one_mul]
  exact upperMobiusCoefficient_optimal_one s hR

/-- The transition main quadratic form at the constructed optimal
weights is exactly `1 / G(R)`. -/
theorem transitionMainQuadratic_optimalSelbergWeight
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    transitionMainQuadratic x q R (optimalSelbergWeight s R) =
      (truncatedSelbergMass s R)⁻¹ := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  change transitionMainQuadratic x q R
      (optimalSelbergWeight s R) =
    (truncatedSelbergMass s R)⁻¹
  rw [transitionMainQuadratic_eq_diagonal hx hxEven hq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            s.nu d * smoothingTruncatedWeight R
              (optimalSelbergWeight s R) d
          else 0) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
          (optimalSelbergCoordinate s R l) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp_rw [smoothingTruncatedWeight_optimalSelbergWeight]
      rw [optimalSelbergWeight_coordinate s R
        (Nat.dvd_of_mem_divisors hl)]
    _ = (truncatedSelbergMass s R)⁻¹ :=
      optimalSelbergCoordinate_diagonal s hR

/-- Per-pair transition sieve bound with the optimized main term and a
fully explicit polynomial error. -/
theorem smoothingTransitionSifted_card_le_optimal
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        (truncatedSelbergMass s R)⁻¹ +
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hsieve :=
    smoothingTransitionSifted_card_le_main_add_error hq
      (optimalSelbergWeight s R) hR
      (optimalSelbergWeight_one s hR)
  calc
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          transitionMainQuadratic x q R
            (optimalSelbergWeight s R) +
          transitionErrorQuadratic x q R
            (optimalSelbergWeight s R) := hsieve
    _ ≤ ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s R)⁻¹ +
        ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
          ((R + 1 : ℕ) : ℝ) ^ 2 *
            (3 * (R : ℝ) ^ 2 + 1) := by
      rw [transitionMainQuadratic_optimalSelbergWeight
        hx hxEven hq hR]
      have herr :
          transitionErrorQuadratic x q R
              (optimalSelbergWeight s R) ≤
            ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
              ((R + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (R : ℝ) ^ 2 + 1) := by
        simpa only [s] using
          transitionErrorQuadratic_optimalSelbergWeight_le
            hx hxEven hq hR
      exact add_le_add le_rfl herr

end Chen
