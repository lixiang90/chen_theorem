import ChenTheorem.MainEstimates

open Filter Real
open scoped Classical

namespace Chen

noncomputable def keySievedPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) →
        ¬r ∣ (x - p)

noncomputable def keyChenPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ IsP2 (x - p)

noncomputable def keyMidWitnesses (x : ℕ) :
    Finset (Σ _p' : ℕ, ℕ) :=
  (midPrimes x).sigma fun p' =>
    (Finset.range (x + 1)).filter fun p =>
      p.Prime ∧ p' ∣ (x - p) ∧
        ∀ r : ℕ, r.Prime → 2 < r →
          (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) →
            ¬r ∣ (x - p)

noncomputable def keyOmegaWitnesses (x : ℕ) :
    Finset (Σ _q : ℕ × ℕ, ℕ) :=
  (chenPairs x).sigma fun q => omegaThirdPrimes x q

@[simp]
theorem keySievedPrimes_card (x : ℕ) :
    (keySievedPrimes x).card = sievedPrimeCount x := rfl

@[simp]
theorem keyChenPrimes_card (x : ℕ) :
    (keyChenPrimes x).card = chenCount x := rfl

@[simp]
theorem keyMidWitnesses_card (x : ℕ) :
    (keyMidWitnesses x).card =
      ∑ p' ∈ midPrimes x, sievedPrimeCountAt x p' := by
  unfold keyMidWitnesses sievedPrimeCountAt
  rw [Finset.card_sigma]

@[simp]
theorem keyOmegaWitnesses_card (x : ℕ) :
    (keyOmegaWitnesses x).card = sieveOmega x := by
  unfold keyOmegaWitnesses sieveOmega
  rw [Finset.card_sigma]

noncomputable def keyExceptionalPrimes (x : ℕ) : Finset ℕ :=
  (keySievedPrimes x).filter fun p =>
    p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
      x - p ≤ 1 ∨ ¬Squarefree (x - p)

noncomputable def keyRegularBadPrimes (x : ℕ) : Finset ℕ :=
  (keySievedPrimes x).filter fun p =>
    ¬IsP2 (x - p) ∧
      ¬(p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
        x - p ≤ 1 ∨ ¬Squarefree (x - p))

theorem keySievedPrimes_card_le_partition (x : ℕ) :
    (keySievedPrimes x).card ≤
      (keyChenPrimes x).card +
        (keyExceptionalPrimes x).card +
          (keyRegularBadPrimes x).card := by
  let U :=
    keyChenPrimes x ∪
      keyExceptionalPrimes x ∪ keyRegularBadPrimes x
  have hsub : keySievedPrimes x ⊆ U := by
    intro p hp
    by_cases hP2 : IsP2 (x - p)
    · change p ∈
        (keyChenPrimes x ∪ keyExceptionalPrimes x) ∪
          keyRegularBadPrimes x
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      unfold keyChenPrimes
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1,
          ⟨(Finset.mem_filter.mp hp).2.1, hP2⟩⟩
    · by_cases hE :
          p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
            x - p ≤ 1 ∨ ¬Squarefree (x - p)
      · change p ∈
          (keyChenPrimes x ∪ keyExceptionalPrimes x) ∪
            keyRegularBadPrimes x
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hp, hE⟩
      · change p ∈
          (keyChenPrimes x ∪ keyExceptionalPrimes x) ∪
            keyRegularBadPrimes x
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hp, hP2, hE⟩
  calc
    (keySievedPrimes x).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ (keyChenPrimes x).card +
        (keyExceptionalPrimes x).card +
          (keyRegularBadPrimes x).card := by
      dsimp only [U]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _)
          (keyRegularBadPrimes x).card)

theorem natCast_le_rpow_third_of_cube_le
    {a x : ℕ} (h : a ^ 3 ≤ x) :
    (a : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [show (1 : ℝ) / 3 = (3 : ℝ)⁻¹ by norm_num,
    Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 3)]
  simpa [Real.rpow_natCast] using (by exact_mod_cast h :
    (a : ℝ) ^ 3 ≤ x)

theorem keySieved_primeFactor_gt_threshold
    {x p r : ℕ} (hxEven : Even x) (hpne : p ≠ 2)
    (hp : p ∈ keySievedPrimes x)
    (hrPrime : r.Prime) (hrdiv : r ∣ x - p) :
    (x : ℝ) ^ ((1 : ℝ) / 10) < r := by
  have hpData := Finset.mem_filter.mp hp
  have hple : p ≤ x := by
    have := Finset.mem_range.mp hpData.1
    omega
  have hpOdd : Odd p := hpData.2.1.odd_of_ne_two hpne
  have hnOdd : Odd (x - p) :=
    Nat.Even.sub_odd hple hxEven hpOdd
  have hrTwo : 2 < r := by
    have hrTwoLe := hrPrime.two_le
    by_contra h
    have hre : r = 2 := by omega
    subst r
    exact (Nat.not_even_iff_odd.mpr hnOdd)
      (even_iff_two_dvd.mpr hrdiv)
  by_contra h
  exact hpData.2.2 r hrPrime hrTwo (le_of_not_gt h) hrdiv

theorem keyRegularBadPrimes_classification
    {x p : ℕ} (hxEven : Even x)
    (hp : p ∈ keyRegularBadPrimes x) :
    (∃ a b : ℕ, a ≠ b ∧
        a ∈ midPrimes x ∧ b ∈ midPrimes x ∧
          a ∣ x - p ∧ b ∣ x - p) ∨
      ∃ a b c : ℕ,
        (a, b) ∈ chenPairs x ∧
          c ∈ omegaThirdPrimes x (a, b) ∧
            x - p = a * b * c := by
  have hpReg := Finset.mem_filter.mp hp
  have hpSieved := hpReg.1
  have hpSievedData := Finset.mem_filter.mp hpSieved
  have hpPrime := hpSievedData.2.1
  have hple : p ≤ x := by
    have := Finset.mem_range.mp hpSievedData.1
    omega
  have hnotP2 := hpReg.2.1
  have hregular := hpReg.2.2
  simp only [not_or] at hregular
  have hpne : p ≠ 2 := hregular.1
  have hpLarge :
      (x : ℝ) ^ (0.9 : ℝ) < p :=
    lt_of_not_ge hregular.2.1
  have hnTwo : 1 < x - p :=
    lt_of_not_ge hregular.2.2.1
  have hnSquarefree : Squarefree (x - p) :=
    not_not.mp hregular.2.2.2
  let n := x - p
  have hnzero : n ≠ 0 := by
    dsimp only [n]
    omega
  have hprod := Nat.prod_primeFactorsList hnzero
  have hsorted := Nat.primeFactorsList_sorted n
  have hnodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList hnzero).mp
      hnSquarefree
  cases hlist : n.primeFactorsList with
  | nil =>
      rw [hlist] at hprod
      simp only [List.prod_nil] at hprod
      dsimp only [n] at hprod
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have haPrime : a.Prime :=
            Nat.prime_of_mem_primeFactorsList (by
              rw [hlist]
              simp)
          rw [hlist] at hprod
          simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
          exfalso
          apply hnotP2
          left
          simpa only [n, hprod] using haPrime
      | cons b tail =>
          cases tail with
          | nil =>
              have haPrime : a.Prime :=
                Nat.prime_of_mem_primeFactorsList (by
                  rw [hlist]
                  simp)
              have hbPrime : b.Prime :=
                Nat.prime_of_mem_primeFactorsList (by
                  rw [hlist]
                  simp)
              rw [hlist] at hprod
              simp only [List.prod_cons, List.prod_nil,
                mul_one] at hprod
              exfalso
              apply hnotP2
              right
              exact ⟨a, b, haPrime, hbPrime, by
                dsimp only [n] at hprod
                omega⟩
          | cons c rest =>
              have haPrime : a.Prime :=
                Nat.prime_of_mem_primeFactorsList (by
                  rw [hlist]
                  simp)
              have hbPrime : b.Prime :=
                Nat.prime_of_mem_primeFactorsList (by
                  rw [hlist]
                  simp)
              have hcPrime : c.Prime :=
                Nat.prime_of_mem_primeFactorsList (by
                  rw [hlist]
                  simp)
              rw [hlist] at hsorted hnodup hprod
              simp only [List.prod_cons] at hprod
              have hab : a ≤ b := by
                simpa using hsorted.pairwise.rel_get_of_lt
                  (a := ⟨0, by simp⟩) (b := ⟨1, by simp⟩)
                  (by simp)
              have hbc : b ≤ c := by
                simpa using hsorted.pairwise.rel_get_of_lt
                  (a := ⟨1, by simp⟩) (b := ⟨2, by simp⟩)
                  (by change (1 : ℕ) < 2; norm_num)
              have habne : a ≠ b := by
                intro heq
                subst b
                simp at hnodup
              have habcDiv : a * b * c ∣ n := by
                refine ⟨rest.prod, ?_⟩
                calc
                  n = a * (b * (c * rest.prod)) := hprod.symm
                  _ = a * b * c * rest.prod := by ring
              have hnpos : 0 < n := by
                dsimp only [n]
                omega
              have habcLe : a * b * c ≤ n :=
                Nat.le_of_dvd hnpos habcDiv
              have hac : a ≤ c := hab.trans hbc
              have hacube : a ^ 3 ≤ n := by
                calc
                  a ^ 3 = a * a * a := by ring
                  _ ≤ a * b * c := by gcongr
                  _ ≤ n := habcLe
              have hnle : n ≤ x := by
                dsimp only [n]
                omega
              have haUpper :
                  (a : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
                natCast_le_rpow_third_of_cube_le
                  (hacube.trans hnle)
              have haDiv : a ∣ x - p := by
                have haabc : a ∣ a * b * c :=
                  ⟨b * c, by ring⟩
                exact haabc.trans (by
                  simpa only [n] using habcDiv)
              have hbDiv : b ∣ x - p := by
                have : b ∣ a * b * c := by
                  exact ⟨a * c, by ring⟩
                exact this.trans (by simpa only [n] using habcDiv)
              have haLower :
                  (x : ℝ) ^ ((1 : ℝ) / 10) < a :=
                keySieved_primeFactor_gt_threshold
                  hxEven hpne hpSieved haPrime haDiv
              have hbLower :
                  (x : ℝ) ^ ((1 : ℝ) / 10) < b :=
                keySieved_primeFactor_gt_threshold
                  hxEven hpne hpSieved hbPrime hbDiv
              by_cases hbUpper :
                  (b : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3)
              · left
                refine ⟨a, b, habne, ?_, ?_, haDiv, hbDiv⟩
                · unfold midPrimes
                  apply Finset.mem_filter.mpr
                  exact ⟨Finset.mem_range.mpr (by
                    have := Nat.le_of_dvd
                      (by dsimp only [n] at hnpos ⊢; omega) haDiv
                    omega),
                    haPrime, haLower, haUpper⟩
                · unfold midPrimes
                  apply Finset.mem_filter.mpr
                  exact ⟨Finset.mem_range.mpr (by
                    have := Nat.le_of_dvd
                      (by dsimp only [n] at hnpos ⊢; omega) hbDiv
                    omega),
                    hbPrime, hbLower, hbUpper⟩
              · have hrest : rest = [] := by
                  by_contra hne
                  obtain ⟨d, tail, rfl⟩ :=
                    List.exists_cons_of_ne_nil hne
                  have hdPrime : d.Prime :=
                    Nat.prime_of_mem_primeFactorsList (by
                      rw [hlist]
                      simp)
                  have hcd : c ≤ d := by
                    simpa using hsorted.pairwise.rel_get_of_lt
                      (a := ⟨2, by simp⟩) (b := ⟨3, by simp⟩)
                      (by simp)
                  have habcdDiv : a * b * c * d ∣ n := by
                    refine ⟨tail.prod, ?_⟩
                    calc
                      n = a * (b * (c * (d * tail.prod))) :=
                        hprod.symm
                      _ = a * b * c * d * tail.prod := by ring
                  have habcdLe : a * b * c * d ≤ x :=
                    (Nat.le_of_dvd hnpos habcdDiv).trans hnle
                  have hxone : (1 : ℝ) < x := by
                    have hpone : 1 < p := hpPrime.one_lt
                    exact_mod_cast hpone.trans_le hple
                  have hroot :
                      ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = x := by
                    rw [← Real.rpow_natCast,
                      ← Real.rpow_mul (by positivity)]
                    norm_num
                  have hbRoot :
                      (x : ℝ) ^ ((1 : ℝ) / 3) < b :=
                    lt_of_not_ge hbUpper
                  have hbcd :
                      (x : ℝ) < (b : ℝ) * c * d := by
                    calc
                      (x : ℝ) =
                          ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 :=
                        hroot.symm
                      _ < (b : ℝ) ^ 3 :=
                        pow_lt_pow_left₀ hbRoot (by positivity)
                          (by norm_num : 3 ≠ 0)
                      _ ≤ (b : ℝ) * c * d := by
                        have hnat : b ^ 3 ≤ b * c * d := by
                          calc
                            b ^ 3 = b * b * b := by ring
                            _ ≤ b * c * b :=
                              Nat.mul_le_mul_right b
                                (Nat.mul_le_mul_left b hbc)
                            _ ≤ b * c * d :=
                              Nat.mul_le_mul_left (b * c)
                                (hbc.trans hcd)
                        exact_mod_cast hnat
                  have haone : (1 : ℝ) ≤ a := by
                    exact_mod_cast haPrime.one_le
                  have htooLarge :
                      (x : ℝ) < a * b * c * d := by
                    calc
                      (x : ℝ) < (b : ℝ) * c * d := hbcd
                      _ ≤ (a : ℝ) * b * c * d := by
                        nlinarith [mul_nonneg
                          (show (0 : ℝ) ≤ b by positivity)
                          (show (0 : ℝ) ≤ (c : ℝ) * d by positivity)]
                  exact (not_lt_of_ge (by exact_mod_cast habcdLe))
                    htooLarge
                subst rest
                have habcn : a * b * c = n := by
                  calc
                    a * b * c = a * (b * c) := by ring
                    _ = n := by simpa using hprod
                right
                refine ⟨a, b, c, ?_, ?_, ?_⟩
                · unfold chenPairs
                  apply Finset.mem_filter.mpr
                  have haRange : a < x + 1 := by
                    have := Nat.le_of_dvd
                      (by dsimp only [n] at hnpos ⊢; omega) haDiv
                    omega
                  have hbRange : b < x + 1 := by
                    have := Nat.le_of_dvd
                      (by dsimp only [n] at hnpos ⊢; omega) hbDiv
                    omega
                  refine ⟨Finset.mem_product.mpr
                    ⟨Finset.mem_range.mpr haRange,
                      Finset.mem_range.mpr hbRange⟩,
                    haPrime, hbPrime, haLower, haUpper,
                    lt_of_not_ge hbUpper, ?_⟩
                  have haPos : (0 : ℝ) < a := by
                    exact_mod_cast haPrime.pos
                  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
                    Real.le_rpow_inv_iff_of_pos
                      (by positivity) (by positivity)
                      (by norm_num : (0 : ℝ) < 2)]
                  rw [Real.rpow_two]
                  apply (le_div_iff₀ haPos).2
                  have hbsq : a * b ^ 2 ≤ a * b * c := by
                    calc
                      a * b ^ 2 = (a * b) * b := by ring
                      _ ≤ (a * b) * c :=
                        Nat.mul_le_mul_left (a * b) hbc
                      _ = a * b * c := by ring
                  calc
                    (b : ℝ) ^ 2 * (a : ℝ) =
                        (a * b ^ 2 : ℕ) := by
                      norm_num
                      ring
                    _ ≤ (a * b * c : ℕ) := by
                      exact_mod_cast hbsq
                    _ = n := by exact_mod_cast habcn
                    _ ≤ x := by exact_mod_cast hnle
                · unfold omegaThirdPrimes
                  apply Finset.mem_filter.mpr
                  have hcRange : c < x + 1 := by
                    have hcDiv : c ∣ n := by
                      exact ⟨a * b, by
                        rw [← habcn]
                        ring⟩
                    have := Nat.le_of_dvd hnpos hcDiv
                    omega
                  refine ⟨Finset.mem_range.mpr hcRange,
                    hcPrime, ?_, ?_⟩
                  · have habPos :
                        (0 : ℝ) < (a : ℝ) * b := by
                      exact mul_pos
                        (by exact_mod_cast haPrime.pos)
                        (by exact_mod_cast hbPrime.pos)
                    apply (le_div_iff₀ habPos).2
                    have : c * (a * b) ≤ x := by
                      calc
                        c * (a * b) = a * b * c := by ring
                        _ = n := habcn
                        _ ≤ x := hnle
                    exact_mod_cast this
                  · have hrem : x - a * b * c = p := by
                      dsimp only [n] at habcn
                      omega
                    rw [hrem]
                    intro r hrPrime hrSmall hrdiv
                    have hrEq : r = p := by
                      rcases (Nat.dvd_prime hpPrime).mp hrdiv with
                        hrOne | hrEq
                      · exact (hrPrime.ne_one hrOne).elim
                      · exact hrEq
                    subst r
                    have hxBase : (1 : ℝ) ≤ x := by
                      exact_mod_cast (show 1 ≤ x by omega)
                    have hquarterNine :
                        (x : ℝ) ^ ((1 : ℝ) / 4) ≤
                          (x : ℝ) ^ (0.9 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le hxBase
                        (by norm_num)
                    exact (not_le_of_gt hpLarge)
                      (hrSmall.trans hquarterNine)
                · simpa only [n] using habcn.symm

theorem chenPairs_fst_mem_midPrimes
    {x a b : ℕ} (h : (a, b) ∈ chenPairs x) :
    a ∈ midPrimes x := by
  unfold chenPairs at h
  rcases Finset.mem_filter.mp h with
    ⟨habRange, haPrime, _hbPrime, haLower, haUpper, _⟩
  unfold midPrimes
  apply Finset.mem_filter.mpr
  exact ⟨(Finset.mem_product.mp habRange).1,
    haPrime, haLower, haUpper⟩

noncomputable def keyCorrectionWitnesses (x : ℕ) :
    Finset (Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ)) :=
  (keyMidWitnesses x).disjSum (keyOmegaWitnesses x)

@[simp]
theorem keyCorrectionWitnesses_card (x : ℕ) :
    (keyCorrectionWitnesses x).card =
      (keyMidWitnesses x).card + (keyOmegaWitnesses x).card := by
  unfold keyCorrectionWitnesses
  exact Finset.card_disjSum _ _

def keyWitnessPrime (x : ℕ) :
    Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) → ℕ
  | .inl w => w.2
  | .inr w => x - w.1.1 * w.1.2 * w.2

theorem exists_two_keyCorrectionWitnesses
    {x p : ℕ} (hxEven : Even x)
    (hp : p ∈ keyRegularBadPrimes x) :
    ∃ w₀ w₁,
      w₀ ∈ keyCorrectionWitnesses x ∧
        w₁ ∈ keyCorrectionWitnesses x ∧
          w₀ ≠ w₁ ∧
            keyWitnessPrime x w₀ = p ∧
              keyWitnessPrime x w₁ = p := by
  rcases keyRegularBadPrimes_classification hxEven hp with
    hmid | homega
  · rcases hmid with
      ⟨a, b, habne, haMid, hbMid, haDiv, hbDiv⟩
    let w₀ :
        Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
      .inl ⟨a, p⟩
    let w₁ :
        Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
      .inl ⟨b, p⟩
    refine ⟨w₀, w₁, ?_, ?_, ?_, rfl, rfl⟩
    · unfold keyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨a, p⟩, ?_, rfl⟩
      unfold keyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨haMid, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved :=
        (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, haDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · unfold keyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨b, p⟩, ?_, rfl⟩
      unfold keyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨hbMid, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved :=
        (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, hbDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · intro heq
      simp only [w₀, w₁, Sum.inl.injEq,
        Sigma.mk.inj_iff] at heq
      exact habne heq.1
  · rcases homega with
      ⟨a, b, c, habPair, hcOmega, hxp⟩
    let w₀ :
        Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
      .inl ⟨a, p⟩
    let w₁ :
        Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
      .inr ⟨(a, b), c⟩
    refine ⟨w₀, w₁, ?_, ?_, by simp [w₀, w₁],
      rfl, ?_⟩
    · unfold keyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨a, p⟩, ?_, rfl⟩
      unfold keyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨chenPairs_fst_mem_midPrimes habPair, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved :=
        (Finset.mem_filter.mp hp).1
      have haDiv : a ∣ x - p := by
        rw [hxp]
        exact ⟨b * c, by ring⟩
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, haDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · unfold keyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      right
      refine ⟨⟨(a, b), c⟩, ?_, rfl⟩
      unfold keyOmegaWitnesses
      apply Finset.mem_sigma.mpr
      exact ⟨habPair, hcOmega⟩
    · simp only [w₁, keyWitnessPrime]
      have hpSieved := (Finset.mem_filter.mp hp).1
      have hple : p ≤ x := by
        have := Finset.mem_range.mp
          (Finset.mem_filter.mp hpSieved).1
        omega
      omega

noncomputable def keyCorrectionWitness
    (x : ℕ) (hxEven : Even x)
    (p : {p // p ∈ keyRegularBadPrimes x}) (i : Fin 2) :
    Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
  if i = 0 then
    Classical.choose
      (exists_two_keyCorrectionWitnesses hxEven p.property)
  else
    Classical.choose (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))

theorem keyCorrectionWitness_mem
    (x : ℕ) (hxEven : Even x)
    (p : {p // p ∈ keyRegularBadPrimes x}) (i : Fin 2) :
    keyCorrectionWitness x hxEven p i ∈
      keyCorrectionWitnesses x := by
  by_cases hi : i = 0
  · simp only [keyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))).1
  · simp only [keyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))).2.1

theorem keyCorrectionWitness_prime
    (x : ℕ) (hxEven : Even x)
    (p : {p // p ∈ keyRegularBadPrimes x}) (i : Fin 2) :
    keyWitnessPrime x (keyCorrectionWitness x hxEven p i) = p := by
  by_cases hi : i = 0
  · simp only [keyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))).2.2.2.1
  · simp only [keyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))).2.2.2.2

theorem keyCorrectionWitness_ne
    (x : ℕ) (hxEven : Even x)
    (p : {p // p ∈ keyRegularBadPrimes x}) :
    keyCorrectionWitness x hxEven p 0 ≠
      keyCorrectionWitness x hxEven p 1 := by
  simpa [keyCorrectionWitness] using
    (Classical.choose_spec (Classical.choose_spec
      (exists_two_keyCorrectionWitnesses hxEven p.property))).2.2.1

theorem keyCorrectionWitness_injective
    (x : ℕ) (hxEven : Even x) :
    Function.Injective fun z :
        {p // p ∈ keyRegularBadPrimes x} × Fin 2 =>
      (⟨keyCorrectionWitness x hxEven z.1 z.2,
        keyCorrectionWitness_mem x hxEven z.1 z.2⟩ :
          {w // w ∈ keyCorrectionWitnesses x}) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  have hpq : (p : ℕ) = q := by
    have hw :
        keyCorrectionWitness x hxEven p i =
          keyCorrectionWitness x hxEven q j :=
      congrArg Subtype.val h
    have := congrArg (keyWitnessPrime x) hw
    simpa only [keyCorrectionWitness_prime] using this
  have hpqSubtype : p = q := Subtype.ext hpq
  subst q
  have hij : i = j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact (keyCorrectionWitness_ne x hxEven p
        (congrArg Subtype.val h)).elim
    · exact (keyCorrectionWitness_ne x hxEven p
        (congrArg Subtype.val h).symm).elim
    · rfl
  subst j
  rfl

theorem two_mul_keyRegularBadPrimes_card_le
    (x : ℕ) (hxEven : Even x) :
    2 * (keyRegularBadPrimes x).card ≤
      (keyMidWitnesses x).card +
        (keyOmegaWitnesses x).card := by
  let f := fun z :
      {p // p ∈ keyRegularBadPrimes x} × Fin 2 =>
    (⟨keyCorrectionWitness x hxEven z.1 z.2,
      keyCorrectionWitness_mem x hxEven z.1 z.2⟩ :
        {w // w ∈ keyCorrectionWitnesses x})
  have hcard := Fintype.card_le_of_injective f
    (keyCorrectionWitness_injective x hxEven)
  simpa [Fintype.card_prod, keyCorrectionWitnesses_card,
    Nat.mul_comm] using hcard

theorem sum_inv_sq_Icc_tail_le
    {Y X : ℕ} (hY : 2 ≤ Y) :
    ∑ q ∈ Finset.Icc Y X, ((q : ℝ) ^ 2)⁻¹ ≤
      ((Y - 1 : ℕ) : ℝ)⁻¹ := by
  by_cases hYX : Y ≤ X
  · have hstrong :
        ∑ q ∈ Finset.Icc Y X, ((q : ℝ) ^ 2)⁻¹ ≤
          ((Y - 1 : ℕ) : ℝ)⁻¹ - (X : ℝ)⁻¹ := by
      induction X, hYX using Nat.le_induction with
      | base =>
          simp only [Finset.Icc_self, Finset.sum_singleton]
          have hYm1pos : (0 : ℝ) < ((Y - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < Y - 1 by omega)
          have hYpos : (0 : ℝ) < Y := by positivity
          have hcast :
              ((Y - 1 : ℕ) : ℝ) = (Y : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          have heq :
              ((Y - 1 : ℕ) : ℝ)⁻¹ - (Y : ℝ)⁻¹ =
                (((Y - 1 : ℕ) : ℝ) * (Y : ℝ))⁻¹ := by
            field_simp [hYm1pos.ne', hYpos.ne']
            rw [hcast]
            ring
          rw [heq]
          simp only [inv_eq_one_div]
          apply one_div_le_one_div_of_le
            (mul_pos hYm1pos hYpos)
          rw [hcast]
          nlinarith
      | succ X hYX ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          have hXpos : (0 : ℝ) < X := by
            exact_mod_cast (show 0 < X by omega)
          have hXspos : (0 : ℝ) < X + 1 := by positivity
          have hstep :
              ((((X + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤
                (X : ℝ)⁻¹ - ((X + 1 : ℕ) : ℝ)⁻¹ := by
            field_simp
            norm_num only [Nat.cast_add, Nat.cast_one] at *
            nlinarith
          linarith
    exact hstrong.trans (sub_le_self _ (by positivity))
  · have hempty : Finset.Icc Y X = ∅ :=
      Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

noncomputable def keySmallExceptionalPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ)

noncomputable def keyEndpointExceptionalPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p = 2 ∨ x - p ≤ 1

noncomputable def keyNonsquarefreeExceptionalPrimes
    (x : ℕ) : Finset ℕ :=
  (keySievedPrimes x).filter fun p =>
    p ≠ 2 ∧ 1 < x - p ∧ ¬Squarefree (x - p)

noncomputable def keyRoughSquareWitnesses (x : ℕ) :
    Finset (Σ _q : ℕ, ℕ) :=
  (Finset.Icc
      (⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1) x).sigma fun q =>
    Finset.Icc 1 (x / (q * q))

@[simp]
theorem keyRoughSquareWitnesses_card (x : ℕ) :
    (keyRoughSquareWitnesses x).card =
      ∑ q ∈ Finset.Icc
          (⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1) x,
        x / (q * q) := by
  unfold keyRoughSquareWitnesses
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  simp

noncomputable def keyRoughSquareWitness
    (x p : ℕ) : Σ _q : ℕ, ℕ :=
  let q := repeatedPrime (x - p)
  ⟨q, (x - p) / (q * q)⟩

theorem keyRoughSquareWitness_mem
    {x p : ℕ} (hxEven : Even x)
    (hp : p ∈ keyNonsquarefreeExceptionalPrimes x) :
    keyRoughSquareWitness x p ∈
      keyRoughSquareWitnesses x := by
  have hpData := Finset.mem_filter.mp hp
  have hpSieved := hpData.1
  have hpne := hpData.2.1
  have hnTwo := hpData.2.2.1
  have hnNot := hpData.2.2.2
  let q := repeatedPrime (x - p)
  have hqPrime : q.Prime := repeatedPrime_prime hnNot
  have hqSqDiv : q * q ∣ x - p :=
    repeatedPrime_sq_dvd hnNot
  have hple : p ≤ x := by
    have hpRange :=
      (Finset.mem_filter.mp hpSieved).1
    have := Finset.mem_range.mp hpRange
    omega
  have hnpos : 0 < x - p := by omega
  have hqSqLe : q * q ≤ x - p :=
    Nat.le_of_dvd hnpos hqSqDiv
  have hqLe : q ≤ x := by
    have hqq : q ≤ q * q := by
      nlinarith [hqPrime.two_le]
    omega
  have hqLowerReal :
      (x : ℝ) ^ ((1 : ℝ) / 10) < q :=
    keySieved_primeFactor_gt_threshold
      hxEven hpne hpSieved hqPrime
        ((show q ∣ q * q from ⟨q, rfl⟩).trans hqSqDiv)
  have hqLower :
      ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1 ≤ q := by
    have hfloor :
        ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ < q :=
      (Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).2
        hqLowerReal
    omega
  unfold keyRoughSquareWitnesses keyRoughSquareWitness
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hqLower, hqLe⟩, ?_⟩
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.div_pos hqSqLe
      (Nat.mul_pos hqPrime.pos hqPrime.pos)
  · exact Nat.div_le_div_right (by omega : x - p ≤ x)

theorem keyRoughSquareWitness_injective
    (x : ℕ) :
    Set.InjOn (keyRoughSquareWitness x)
      (keyNonsquarefreeExceptionalPrimes x) := by
  intro p hp r hr hpr
  have hpData := Finset.mem_filter.mp hp
  have hrData := Finset.mem_filter.mp hr
  have hpSieved := hpData.1
  have hrSieved := hrData.1
  have hpNot := hpData.2.2.2
  have hrNot := hrData.2.2.2
  have hpDiv := repeatedPrime_sq_dvd hpNot
  have hrDiv := repeatedPrime_sq_dvd hrNot
  have hpProd :
      repeatedPrime (x - p) * repeatedPrime (x - p) *
          ((x - p) /
            (repeatedPrime (x - p) * repeatedPrime (x - p))) =
        x - p := by
    exact Nat.mul_div_cancel' hpDiv
  have hrProd :
      repeatedPrime (x - r) * repeatedPrime (x - r) *
          ((x - r) /
            (repeatedPrime (x - r) * repeatedPrime (x - r))) =
        x - r := by
    exact Nat.mul_div_cancel' hrDiv
  have hnEq : x - p = x - r := by
    have := congrArg
      (fun z : Σ _q : ℕ, ℕ => z.1 * z.1 * z.2) hpr
    simpa only [keyRoughSquareWitness, hpProd, hrProd] using this
  have hple : p ≤ x := by
    have := Finset.mem_range.mp
      (Finset.mem_filter.mp hpSieved).1
    omega
  have hrle : r ≤ x := by
    have := Finset.mem_range.mp
      (Finset.mem_filter.mp hrSieved).1
    omega
  omega

theorem keyNonsquarefreeExceptionalPrimes_card_le
    (x : ℕ) (hxEven : Even x) :
    (keyNonsquarefreeExceptionalPrimes x).card ≤
      (keyRoughSquareWitnesses x).card := by
  let f := fun p :
      {p // p ∈ keyNonsquarefreeExceptionalPrimes x} =>
    (⟨keyRoughSquareWitness x p,
      keyRoughSquareWitness_mem hxEven p.property⟩ :
        {w // w ∈ keyRoughSquareWitnesses x})
  have hf : Function.Injective f := by
    intro p r h
    apply Subtype.ext
    apply keyRoughSquareWitness_injective x p.property r.property
    exact congrArg Subtype.val h
  simpa using Fintype.card_le_of_injective f hf

theorem keyExceptionalPrimes_card_le_parts (x : ℕ) :
    (keyExceptionalPrimes x).card ≤
      (keySmallExceptionalPrimes x).card +
        (keyEndpointExceptionalPrimes x).card +
          (keyNonsquarefreeExceptionalPrimes x).card := by
  let U :=
    keySmallExceptionalPrimes x ∪
      keyEndpointExceptionalPrimes x ∪
        keyNonsquarefreeExceptionalPrimes x
  have hsub : keyExceptionalPrimes x ⊆ U := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpSieved := hpData.1
    have hpRange := (Finset.mem_filter.mp hpSieved).1
    rcases hpData.2 with hpTwo | hpSmall | hpEnd | hpNot
    · have hmem : p ∈ keyEndpointExceptionalPrimes x := by
        unfold keyEndpointExceptionalPrimes
        exact Finset.mem_filter.mpr ⟨hpRange, Or.inl hpTwo⟩
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
    · have hmem : p ∈ keySmallExceptionalPrimes x := by
        unfold keySmallExceptionalPrimes
        exact Finset.mem_filter.mpr ⟨hpRange, hpSmall⟩
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl hmem)))
    · have hmem : p ∈ keyEndpointExceptionalPrimes x := by
        unfold keyEndpointExceptionalPrimes
        exact Finset.mem_filter.mpr ⟨hpRange, Or.inr hpEnd⟩
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
    · by_cases hpTwo : p = 2
      · have hmem : p ∈ keyEndpointExceptionalPrimes x := by
          unfold keyEndpointExceptionalPrimes
          exact Finset.mem_filter.mpr ⟨hpRange, Or.inl hpTwo⟩
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
      · by_cases hpEnd : x - p ≤ 1
        · have hmem : p ∈ keyEndpointExceptionalPrimes x := by
            unfold keyEndpointExceptionalPrimes
            exact Finset.mem_filter.mpr ⟨hpRange, Or.inr hpEnd⟩
          exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
        · have hmem : p ∈ keyNonsquarefreeExceptionalPrimes x := by
            unfold keyNonsquarefreeExceptionalPrimes
            exact Finset.mem_filter.mpr
              ⟨hpSieved, hpTwo, lt_of_not_ge hpEnd, hpNot⟩
          exact Finset.mem_union.mpr (Or.inr hmem)
  calc
    (keyExceptionalPrimes x).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ (keySmallExceptionalPrimes x).card +
        (keyEndpointExceptionalPrimes x).card +
          (keyNonsquarefreeExceptionalPrimes x).card := by
      dsimp only [U]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _)
          (keyNonsquarefreeExceptionalPrimes x).card)

theorem keySmallExceptionalPrimes_card_real_le (x : ℕ) :
    ((keySmallExceptionalPrimes x).card : ℝ) ≤
      (x : ℝ) ^ (0.9 : ℝ) + 1 := by
  let y : ℝ := (x : ℝ) ^ (0.9 : ℝ)
  have hy : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have hsub :
      keySmallExceptionalPrimes x ⊆
        Finset.range (⌊y⌋₊ + 1) := by
    intro p hp
    have hpSmall :=
      (Finset.mem_filter.mp hp).2
    apply Finset.mem_range.mpr
    have hpfloor : p ≤ ⌊y⌋₊ := by
      rw [Nat.le_floor_iff hy]
      exact hpSmall
    omega
  have hcard :
      (keySmallExceptionalPrimes x).card ≤ ⌊y⌋₊ + 1 := by
    simpa using Finset.card_le_card hsub
  calc
    ((keySmallExceptionalPrimes x).card : ℝ) ≤
        (⌊y⌋₊ + 1 : ℕ) := by exact_mod_cast hcard
    _ ≤ y + 1 := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      simpa [add_comm] using
        (add_le_add_right (Nat.floor_le hy) 1)
    _ = (x : ℝ) ^ (0.9 : ℝ) + 1 := rfl

theorem keyEndpointExceptionalPrimes_card_le (x : ℕ) :
    (keyEndpointExceptionalPrimes x).card ≤ 3 := by
  have hsub :
      keyEndpointExceptionalPrimes x ⊆
        ({2, x, x - 1} : Finset ℕ) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hple : p ≤ x := by
      have := Finset.mem_range.mp hpData.1
      omega
    rcases hpData.2 with rfl | hpEnd
    · simp
    · have : p = x ∨ p = x - 1 := by omega
      rcases this with rfl | rfl <;> simp
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

theorem keyRoughSquareWitnesses_card_real_le
    (x : ℕ)
    (hroot : 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 10)) :
    ((keyRoughSquareWitnesses x).card : ℝ) ≤
      2 * (x : ℝ) ^ (0.9 : ℝ) := by
  let y : ℝ := (x : ℝ) ^ ((1 : ℝ) / 10)
  let Y : ℕ := ⌊y⌋₊ + 1
  have hxpos : (0 : ℝ) < x := by
    by_contra hx
    have hxzero : x = 0 := by
      have hxzeroReal : (x : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hx) (by positivity)
      exact_mod_cast hxzeroReal
    subst x
    norm_num at hroot
  have hypos : 0 < y := by
    dsimp only [y]
    positivity
  have hyTwo : 2 ≤ y := by simpa only [y] using hroot
  have hfloorOne : 1 ≤ ⌊y⌋₊ := by
    by_contra h
    have hlt : ⌊y⌋₊ < 1 := by omega
    have := (Nat.floor_lt_one hypos.le).mp hlt
    linarith
  have hY : 2 ≤ Y := by
    dsimp only [Y]
    omega
  have hsumCast :
      ((∑ q ∈ Finset.Icc Y x, x / (q * q) : ℕ) : ℝ) ≤
        ∑ q ∈ Finset.Icc Y x,
          (x : ℝ) / ((q : ℝ) ^ 2) := by
    push_cast
    apply Finset.sum_le_sum
    intro q hq
    simpa [Nat.cast_mul, pow_two] using
      (Nat.cast_div_le (α := ℝ) (m := x) (n := q * q))
  have hsumFactor :
      (∑ q ∈ Finset.Icc Y x,
          (x : ℝ) / ((q : ℝ) ^ 2)) =
        (x : ℝ) *
          ∑ q ∈ Finset.Icc Y x, ((q : ℝ) ^ 2)⁻¹ := by
    simp_rw [div_eq_mul_inv]
    exact (Finset.mul_sum _ _ _).symm
  have htail :
      ∑ q ∈ Finset.Icc Y x, ((q : ℝ) ^ 2)⁻¹ ≤
        (⌊y⌋₊ : ℝ)⁻¹ := by
    simpa only [Y, Nat.add_sub_cancel] using
      (sum_inv_sq_Icc_tail_le (X := x) hY)
  have hfloorHalf : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
    exact (Nat.div_two_lt_floor
      (show (1 : ℝ) ≤ y by linarith)).le
  have hfloorPos : (0 : ℝ) < ⌊y⌋₊ := by
    exact_mod_cast (show 0 < ⌊y⌋₊ by omega)
  have hpow :
      (x : ℝ) ^ (0.9 : ℝ) * y = x := by
    dsimp only [y]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hxDiv :
      (x : ℝ) * (⌊y⌋₊ : ℝ)⁻¹ ≤
        2 * (x : ℝ) ^ (0.9 : ℝ) := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hfloorPos).2
    calc
      (x : ℝ) = (x : ℝ) ^ (0.9 : ℝ) * y := hpow.symm
      _ = 2 * (x : ℝ) ^ (0.9 : ℝ) * (y / 2) := by ring
      _ ≤ 2 * (x : ℝ) ^ (0.9 : ℝ) * (⌊y⌋₊ : ℝ) := by
        gcongr
  calc
    ((keyRoughSquareWitnesses x).card : ℝ) =
        ((∑ q ∈ Finset.Icc Y x, x / (q * q) : ℕ) : ℝ) := by
      rw [keyRoughSquareWitnesses_card]
    _ ≤ ∑ q ∈ Finset.Icc Y x,
          (x : ℝ) / ((q : ℝ) ^ 2) := hsumCast
    _ = (x : ℝ) *
          ∑ q ∈ Finset.Icc Y x, ((q : ℝ) ^ 2)⁻¹ := hsumFactor
    _ ≤ (x : ℝ) * (⌊y⌋₊ : ℝ)⁻¹ := by gcongr
    _ ≤ 2 * (x : ℝ) ^ (0.9 : ℝ) := hxDiv

/-- The exceptional part of (28).  Its proof is the remaining elementary
tail estimate: a nonsquarefree survivor has a repeated prime divisor
`q > x^(1/10)`, and summing `x / q²` gives `O(x^0.9)`.  Together with the
primes `p ≤ x^0.9` and the finitely many endpoint cases this is eventually
at most `x^0.91`. -/
theorem eventually_keyExceptionalPrimes_card_le :
    ∀ᶠ x : ℕ in atTop,
      Even x →
        ((keyExceptionalPrimes x).card : ℝ) ≤
          (x : ℝ) ^ (0.91 : ℝ) := by
  have hrootReal :
      ∀ᶠ y : ℝ in atTop,
        2 ≤ y ^ ((1 : ℝ) / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 2)
  have hroot :=
    tendsto_natCast_atTop_atTop.eventually hrootReal
  have hbonusReal :
      ∀ᶠ y : ℝ in atTop,
        7 ≤ y ^ (0.01 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).eventually
      (eventually_ge_atTop 7)
  have hbonus :=
    tendsto_natCast_atTop_atTop.eventually hbonusReal
  filter_upwards [hroot, hbonus, eventually_ge_atTop 1] with
      x hroot hbonus hx
  intro hxEven
  have hparts := keyExceptionalPrimes_card_le_parts x
  have hpartsReal :
      ((keyExceptionalPrimes x).card : ℝ) ≤
        (keySmallExceptionalPrimes x).card +
          (keyEndpointExceptionalPrimes x).card +
            (keyNonsquarefreeExceptionalPrimes x).card := by
    exact_mod_cast hparts
  have hsmall :=
    keySmallExceptionalPrimes_card_real_le x
  have hend :
      ((keyEndpointExceptionalPrimes x).card : ℝ) ≤ 3 := by
    exact_mod_cast keyEndpointExceptionalPrimes_card_le x
  have hnonsquare :
      ((keyNonsquarefreeExceptionalPrimes x).card : ℝ) ≤
        2 * (x : ℝ) ^ (0.9 : ℝ) := by
    have hcard :=
      keyNonsquarefreeExceptionalPrimes_card_le x
        hxEven
    have hcardReal :
        ((keyNonsquarefreeExceptionalPrimes x).card : ℝ) ≤
          (keyRoughSquareWitnesses x).card := by
      exact_mod_cast hcard
    exact hcardReal.trans
      (keyRoughSquareWitnesses_card_real_le x (by simpa using hroot))
  have hxBase : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpowNineOne :
      (1 : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) :=
    Real.one_le_rpow hxBase (by norm_num)
  have hxpos : (0 : ℝ) < x :=
    zero_lt_one.trans_le hxBase
  have hpow :
      (x : ℝ) ^ (0.01 : ℝ) *
          (x : ℝ) ^ (0.9 : ℝ) =
        (x : ℝ) ^ (0.91 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  calc
    ((keyExceptionalPrimes x).card : ℝ) ≤
        (keySmallExceptionalPrimes x).card +
          (keyEndpointExceptionalPrimes x).card +
            (keyNonsquarefreeExceptionalPrimes x).card :=
      hpartsReal
    _ ≤ ((x : ℝ) ^ (0.9 : ℝ) + 1) + 3 +
          2 * (x : ℝ) ^ (0.9 : ℝ) := by gcongr
    _ ≤ 7 * (x : ℝ) ^ (0.9 : ℝ) := by
      nlinarith
    _ ≤ (x : ℝ) ^ (0.01 : ℝ) *
          (x : ℝ) ^ (0.9 : ℝ) := by gcongr
    _ = (x : ℝ) ^ (0.91 : ℝ) := hpow

/-- The combinatorial form of Chen's key inequality (28), obtained from the
explicit two-witness injection for every regular non-`P₂` survivor and the
exceptional tail estimate above. -/
theorem key_inequality_of_witness_count :
    ∀ᶠ x : ℕ in atTop, Even x →
      (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) -
          (sieveOmega x : ℝ) / 2 -
            (x : ℝ) ^ (0.91 : ℝ) ≤
        (chenCount x : ℝ) := by
  filter_upwards [eventually_keyExceptionalPrimes_card_le] with
      x hExceptional hxEven
  have hPartition := keySievedPrimes_card_le_partition x
  have hWitness :=
    two_mul_keyRegularBadPrimes_card_le x hxEven
  have hPartitionReal :
      ((keySievedPrimes x).card : ℝ) ≤
        (keyChenPrimes x).card +
          (keyExceptionalPrimes x).card +
            (keyRegularBadPrimes x).card := by
    exact_mod_cast hPartition
  have hWitnessReal :
      2 * ((keyRegularBadPrimes x).card : ℝ) ≤
        (keyMidWitnesses x).card +
          (keyOmegaWitnesses x).card := by
    exact_mod_cast hWitness
  rw [keySievedPrimes_card, keyChenPrimes_card] at hPartitionReal
  rw [keyMidWitnesses_card, keyOmegaWitnesses_card] at hWitnessReal
  push_cast at hPartitionReal hWitnessReal
  have hExceptional' := hExceptional hxEven
  nlinarith

end Chen
