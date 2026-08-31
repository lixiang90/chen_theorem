import ChenTheorem.Main.KeyInequality
import ChenTheorem.Main.ShiftedLemma9

open Filter Real
open scoped Classical

namespace Chen

/-! # Fixed-shift analogue of inequality (28) -/

noncomputable def shiftedKeySievedPrimes (h x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) → ¬r ∣ p + h

noncomputable def shiftedKeyChenPrimes (h x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ IsP2 (p + h) ∧ p + h ≤ x

noncomputable def shiftedKeyMidWitnesses (h x : ℕ) :
    Finset (Σ _p' : ℕ, ℕ) :=
  (midPrimes x).sigma fun p' =>
    (Finset.range (x + 1)).filter fun p =>
      p.Prime ∧ p' ∣ p + h ∧
        ∀ r : ℕ, r.Prime → 2 < r →
          (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) → ¬r ∣ p + h

noncomputable def shiftedKeyOmegaWitnesses (h x : ℕ) :
    Finset (Σ _q : ℕ × ℕ, ℕ) :=
  (chenPairs x).sigma fun q => shiftedOmegaThirdPrimes h x q

@[simp] theorem shiftedKeySievedPrimes_card (h x : ℕ) :
    (shiftedKeySievedPrimes h x).card = shiftedSievedPrimeCount h x := rfl

@[simp] theorem shiftedKeyChenPrimes_card (h x : ℕ) :
    (shiftedKeyChenPrimes h x).card = shiftedChenCountCore h x := rfl

@[simp] theorem shiftedKeyMidWitnesses_card (h x : ℕ) :
    (shiftedKeyMidWitnesses h x).card =
      ∑ p' ∈ midPrimes x, shiftedSievedPrimeCountAt h x p' := by
  unfold shiftedKeyMidWitnesses shiftedSievedPrimeCountAt
  rw [Finset.card_sigma]

@[simp] theorem shiftedKeyOmegaWitnesses_card (h x : ℕ) :
    (shiftedKeyOmegaWitnesses h x).card = shiftedSieveOmega h x := by
  unfold shiftedKeyOmegaWitnesses shiftedSieveOmega
  rw [Finset.card_sigma]

noncomputable def shiftedKeyExceptionalPrimes (h x : ℕ) : Finset ℕ :=
  (shiftedKeySievedPrimes h x).filter fun p =>
    p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
      x < p + h ∨ ¬Squarefree (p + h)

noncomputable def shiftedKeyRegularBadPrimes (h x : ℕ) : Finset ℕ :=
  (shiftedKeySievedPrimes h x).filter fun p =>
    ¬IsP2 (p + h) ∧
      ¬(p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
        x < p + h ∨ ¬Squarefree (p + h))

theorem shiftedKeySievedPrimes_card_le_partition (h x : ℕ) :
    (shiftedKeySievedPrimes h x).card ≤
      (shiftedKeyChenPrimes h x).card +
        (shiftedKeyExceptionalPrimes h x).card +
          (shiftedKeyRegularBadPrimes h x).card := by
  let U := shiftedKeyChenPrimes h x ∪
    shiftedKeyExceptionalPrimes h x ∪ shiftedKeyRegularBadPrimes h x
  have hsub : shiftedKeySievedPrimes h x ⊆ U := by
    intro p hp
    by_cases hP2 : IsP2 (p + h)
    · by_cases hle : p + h ≤ x
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        unfold shiftedKeyChenPrimes
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hp).1,
            (Finset.mem_filter.mp hp).2.1, hP2, hle⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr
          ⟨hp, Or.inr (Or.inr (Or.inl (lt_of_not_ge hle)))⟩
    · by_cases hE :
          p = 2 ∨ (p : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) ∨
            x < p + h ∨ ¬Squarefree (p + h)
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hp, hE⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hp, hP2, hE⟩
  calc
    (shiftedKeySievedPrimes h x).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ (shiftedKeyChenPrimes h x).card +
        (shiftedKeyExceptionalPrimes h x).card +
          (shiftedKeyRegularBadPrimes h x).card := by
      dsimp only [U]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _)
          (shiftedKeyRegularBadPrimes h x).card)

theorem shiftedKeySieved_primeFactor_gt_threshold
    {h x p r : ℕ} (hhEven : Even h) (hpne : p ≠ 2)
    (hp : p ∈ shiftedKeySievedPrimes h x)
    (hrPrime : r.Prime) (hrdiv : r ∣ p + h) :
    (x : ℝ) ^ ((1 : ℝ) / 10) < r := by
  have hpData := Finset.mem_filter.mp hp
  have hpOdd : Odd p := hpData.2.1.odd_of_ne_two hpne
  have hnOdd : Odd (p + h) := hpOdd.add_even hhEven
  have hrTwo : 2 < r := by
    have hrTwoLe := hrPrime.two_le
    by_contra hrNot
    have hre : r = 2 := by omega
    subst r
    exact (Nat.not_even_iff_odd.mpr hnOdd) (even_iff_two_dvd.mpr hrdiv)
  by_contra hrNot
  exact hpData.2.2 r hrPrime hrTwo (le_of_not_gt hrNot) hrdiv

/-- Every regular non-`P₂` shifted survivor supplies either two distinct
mid-prime witnesses or one mid-prime witness and one `Ω` witness. -/
theorem shiftedKeyRegularBadPrimes_classification
    {h x p : ℕ} (hh0 : 0 < h) (hhEven : Even h)
    (hp : p ∈ shiftedKeyRegularBadPrimes h x) :
    (∃ a b : ℕ, a ≠ b ∧
        a ∈ midPrimes x ∧ b ∈ midPrimes x ∧
          a ∣ p + h ∧ b ∣ p + h) ∨
      ∃ a b c : ℕ,
        (a, b) ∈ chenPairs x ∧
          c ∈ shiftedOmegaThirdPrimes h x (a, b) ∧
            p + h = a * b * c := by
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
  have hpLarge : (x : ℝ) ^ (0.9 : ℝ) < p :=
    lt_of_not_ge hregular.2.1
  have hnle : p + h ≤ x := le_of_not_gt hregular.2.2.1
  have hnSquarefree : Squarefree (p + h) := not_not.mp hregular.2.2.2
  let n := p + h
  have hnzero : n ≠ 0 := by dsimp only [n]; omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  have hprod := Nat.prod_primeFactorsList hnzero
  have hsorted := Nat.primeFactorsList_sorted n
  have hnodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList hnzero).mp hnSquarefree
  cases hlist : n.primeFactorsList with
  | nil =>
      rw [hlist] at hprod
      simp only [List.prod_nil] at hprod
      dsimp only [n] at hprod
      have hpTwo := hpPrime.two_le
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have haPrime : a.Prime := Nat.prime_of_mem_primeFactorsList (by
            rw [hlist]; simp)
          rw [hlist] at hprod
          simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
          exfalso
          apply hnotP2
          left
          simpa only [n, hprod] using haPrime
      | cons b tail =>
          cases tail with
          | nil =>
              have haPrime : a.Prime := Nat.prime_of_mem_primeFactorsList (by
                rw [hlist]; simp)
              have hbPrime : b.Prime := Nat.prime_of_mem_primeFactorsList (by
                rw [hlist]; simp)
              rw [hlist] at hprod
              simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
              exfalso
              apply hnotP2
              right
              exact ⟨a, b, haPrime, hbPrime, by
                dsimp only [n] at hprod
                omega⟩
          | cons c rest =>
              have haPrime : a.Prime := Nat.prime_of_mem_primeFactorsList (by
                rw [hlist]; simp)
              have hbPrime : b.Prime := Nat.prime_of_mem_primeFactorsList (by
                rw [hlist]; simp)
              have hcPrime : c.Prime := Nat.prime_of_mem_primeFactorsList (by
                rw [hlist]; simp)
              rw [hlist] at hsorted hnodup hprod
              simp only [List.prod_cons] at hprod
              have hab : a ≤ b := by
                simpa using hsorted.pairwise.rel_get_of_lt
                  (a := ⟨0, by simp⟩) (b := ⟨1, by simp⟩) (by simp)
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
              have habcLe : a * b * c ≤ n := Nat.le_of_dvd hnpos habcDiv
              have hacube : a ^ 3 ≤ n := by
                calc
                  a ^ 3 = a * a * a := by ring
                  _ ≤ a * b * c := by
                    gcongr
                    exact hab.trans hbc
                  _ ≤ n := habcLe
              have haUpper :
                  (a : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
                natCast_le_rpow_third_of_cube_le (hacube.trans hnle)
              have haDiv : a ∣ p + h := by
                exact (show a ∣ a * b * c from ⟨b * c, by ring⟩).trans
                  (by simpa only [n] using habcDiv)
              have hbDiv : b ∣ p + h := by
                exact (show b ∣ a * b * c from ⟨a * c, by ring⟩).trans
                  (by simpa only [n] using habcDiv)
              have haLower : (x : ℝ) ^ ((1 : ℝ) / 10) < a :=
                shiftedKeySieved_primeFactor_gt_threshold
                  hhEven hpne hpSieved haPrime haDiv
              have hbLower : (x : ℝ) ^ ((1 : ℝ) / 10) < b :=
                shiftedKeySieved_primeFactor_gt_threshold
                  hhEven hpne hpSieved hbPrime hbDiv
              by_cases hbUpper :
                  (b : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3)
              · left
                refine ⟨a, b, habne, ?_, ?_, haDiv, hbDiv⟩
                · unfold midPrimes
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_range.mpr (by
                      have := Nat.le_of_dvd hnpos haDiv
                      omega), haPrime, haLower, haUpper⟩
                · unfold midPrimes
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_range.mpr (by
                      have := Nat.le_of_dvd hnpos hbDiv
                      omega), hbPrime, hbLower, hbUpper⟩
              · have hrest : rest = [] := by
                  by_contra hne
                  obtain ⟨d, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
                  have hcd : c ≤ d := by
                    simpa using hsorted.pairwise.rel_get_of_lt
                      (a := ⟨2, by simp⟩) (b := ⟨3, by simp⟩) (by simp)
                  have habcdDiv : a * b * c * d ∣ n := by
                    refine ⟨tail.prod, ?_⟩
                    calc
                      n = a * (b * (c * (d * tail.prod))) := hprod.symm
                      _ = a * b * c * d * tail.prod := by ring
                  have habcdLe : a * b * c * d ≤ x :=
                    (Nat.le_of_dvd hnpos habcdDiv).trans hnle
                  have hxone : (1 : ℝ) < x := by
                    exact_mod_cast hpPrime.one_lt.trans_le hple
                  have hroot :
                      ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = x := by
                    rw [← Real.rpow_natCast,
                      ← Real.rpow_mul (by positivity)]
                    norm_num
                  have hbRoot : (x : ℝ) ^ ((1 : ℝ) / 3) < b :=
                    lt_of_not_ge hbUpper
                  have hbcd : (x : ℝ) < (b : ℝ) * c * d := by
                    calc
                      (x : ℝ) = ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := hroot.symm
                      _ < (b : ℝ) ^ 3 :=
                        pow_lt_pow_left₀ hbRoot (by positivity) (by norm_num)
                      _ ≤ (b : ℝ) * c * d := by
                        exact_mod_cast (show b ^ 3 ≤ b * c * d by
                          calc
                            b ^ 3 = b * b * b := by ring
                            _ ≤ b * c * b := by gcongr
                            _ ≤ b * c * d := by
                              gcongr
                              exact hbc.trans hcd)
                  have haone : (1 : ℝ) ≤ a := by exact_mod_cast haPrime.one_le
                  have htooLarge : (x : ℝ) < a * b * c * d := by
                    calc
                      (x : ℝ) < (b : ℝ) * c * d := hbcd
                      _ ≤ (a : ℝ) * b * c * d := by
                        nlinarith [mul_nonneg
                          (show (0 : ℝ) ≤ b by positivity)
                          (show (0 : ℝ) ≤ (c : ℝ) * d by positivity)]
                  exact (not_lt_of_ge (by exact_mod_cast habcdLe)) htooLarge
                subst rest
                have habcn : a * b * c = n := by
                  calc
                    a * b * c = a * (b * c) := by ring
                    _ = n := by simpa using hprod
                right
                refine ⟨a, b, c, ?_, ?_, ?_⟩
                · unfold chenPairs
                  apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_product.mpr
                    ⟨Finset.mem_range.mpr (by
                      have := Nat.le_of_dvd hnpos haDiv
                      omega),
                     Finset.mem_range.mpr (by
                      have := Nat.le_of_dvd hnpos hbDiv
                      omega)⟩,
                    haPrime, hbPrime, haLower, haUpper,
                    lt_of_not_ge hbUpper, ?_⟩
                  have haPos : (0 : ℝ) < a := by exact_mod_cast haPrime.pos
                  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
                    Real.le_rpow_inv_iff_of_pos (by positivity)
                      (by positivity) (by norm_num : (0 : ℝ) < 2)]
                  rw [Real.rpow_two]
                  apply (le_div_iff₀ haPos).2
                  have hbsq : a * b ^ 2 ≤ a * b * c := by
                    calc
                      a * b ^ 2 = (a * b) * b := by ring
                      _ ≤ (a * b) * c := Nat.mul_le_mul_left _ hbc
                      _ = a * b * c := by ring
                  calc
                    (b : ℝ) ^ 2 * (a : ℝ) = (a * b ^ 2 : ℕ) := by
                      norm_num
                      ring
                    _ ≤ (a * b * c : ℕ) := by exact_mod_cast hbsq
                    _ = n := by exact_mod_cast habcn
                    _ ≤ x := by exact_mod_cast hnle
                · unfold shiftedOmegaThirdPrimes
                  apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_range.mpr (by
                    have hcDiv : c ∣ n := ⟨a * b, by rw [← habcn]; ring⟩
                    have := Nat.le_of_dvd hnpos hcDiv
                    omega), hcPrime, ?_, ?_⟩
                  · have haPos : (0 : ℝ) < a := by exact_mod_cast haPrime.pos
                    have hbPos : (0 : ℝ) < b := by exact_mod_cast hbPrime.pos
                    have habPos : (0 : ℝ) < (a : ℝ) * b :=
                      mul_pos haPos hbPos
                    apply (le_div_iff₀ habPos).2
                    exact_mod_cast (show c * (a * b) ≤ x by
                      calc
                        c * (a * b) = a * b * c := by ring
                        _ = n := habcn
                        _ ≤ x := hnle)
                  · unfold shiftedRough
                    have habcEq : a * b * c = p + h := by
                      simpa only [n] using habcn
                    constructor
                    · rw [habcEq]
                      have hp0 : 0 < p := hpPrime.pos
                      omega
                    · rw [habcEq, Nat.add_sub_cancel]
                      intro r hrPrime hrSmall hrdiv
                      have hrEq : r = p := by
                        rcases (Nat.dvd_prime hpPrime).mp hrdiv with hrOne | hrEq
                        · exact (hrPrime.ne_one hrOne).elim
                        · exact hrEq
                      subst r
                      have hxBase : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
                      have hquarterNine :
                          (x : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ (0.9 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_le hxBase (by norm_num)
                      exact (not_le_of_gt hpLarge) (hrSmall.trans hquarterNine)
                · simpa only [n] using habcn.symm

noncomputable def shiftedKeyCorrectionWitnesses (h x : ℕ) :
    Finset (Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ)) :=
  (shiftedKeyMidWitnesses h x).disjSum (shiftedKeyOmegaWitnesses h x)

@[simp] theorem shiftedKeyCorrectionWitnesses_card (h x : ℕ) :
    (shiftedKeyCorrectionWitnesses h x).card =
      (shiftedKeyMidWitnesses h x).card +
        (shiftedKeyOmegaWitnesses h x).card := by
  unfold shiftedKeyCorrectionWitnesses
  exact Finset.card_disjSum _ _

def shiftedKeyWitnessPrime (h : ℕ) :
    Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) → ℕ
  | .inl w => w.2
  | .inr w => w.1.1 * w.1.2 * w.2 - h

theorem exists_two_shiftedKeyCorrectionWitnesses
    {h x p : ℕ} (hh0 : 0 < h) (hhEven : Even h)
    (hp : p ∈ shiftedKeyRegularBadPrimes h x) :
    ∃ w₀ w₁,
      w₀ ∈ shiftedKeyCorrectionWitnesses h x ∧
        w₁ ∈ shiftedKeyCorrectionWitnesses h x ∧
          w₀ ≠ w₁ ∧
            shiftedKeyWitnessPrime h w₀ = p ∧
              shiftedKeyWitnessPrime h w₁ = p := by
  rcases shiftedKeyRegularBadPrimes_classification hh0 hhEven hp with
    hmid | homega
  · rcases hmid with ⟨a, b, habne, haMid, hbMid, haDiv, hbDiv⟩
    let w₀ : Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) := .inl ⟨a, p⟩
    let w₁ : Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) := .inl ⟨b, p⟩
    refine ⟨w₀, w₁, ?_, ?_, ?_, rfl, rfl⟩
    · unfold shiftedKeyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨a, p⟩, ?_, rfl⟩
      unfold shiftedKeyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨haMid, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved := (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, haDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · unfold shiftedKeyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨b, p⟩, ?_, rfl⟩
      unfold shiftedKeyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨hbMid, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved := (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, hbDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · intro heq
      simp only [w₀, w₁, Sum.inl.injEq, Sigma.mk.inj_iff] at heq
      exact habne heq.1
  · rcases homega with ⟨a, b, c, habPair, hcOmega, hpEq⟩
    let w₀ : Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) := .inl ⟨a, p⟩
    let w₁ : Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
      .inr ⟨(a, b), c⟩
    refine ⟨w₀, w₁, ?_, ?_, by simp [w₀, w₁], rfl, ?_⟩
    · unfold shiftedKeyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      left
      refine ⟨⟨a, p⟩, ?_, rfl⟩
      unfold shiftedKeyMidWitnesses
      apply Finset.mem_sigma.mpr
      refine ⟨chenPairs_fst_mem_midPrimes habPair, ?_⟩
      apply Finset.mem_filter.mpr
      have hpSieved := (Finset.mem_filter.mp hp).1
      have haDiv : a ∣ p + h := by
        rw [hpEq]
        exact ⟨b * c, by ring⟩
      exact ⟨(Finset.mem_filter.mp hpSieved).1,
        (Finset.mem_filter.mp hpSieved).2.1, haDiv,
        (Finset.mem_filter.mp hpSieved).2.2⟩
    · unfold shiftedKeyCorrectionWitnesses
      apply Finset.mem_disjSum.mpr
      right
      refine ⟨⟨(a, b), c⟩, ?_, rfl⟩
      unfold shiftedKeyOmegaWitnesses
      exact Finset.mem_sigma.mpr ⟨habPair, hcOmega⟩
    · simp only [w₁, shiftedKeyWitnessPrime]
      omega

noncomputable def shiftedKeyCorrectionWitness
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (p : {p // p ∈ shiftedKeyRegularBadPrimes h x}) (i : Fin 2) :
    Sum (Σ _p' : ℕ, ℕ) (Σ _q : ℕ × ℕ, ℕ) :=
  if i = 0 then
    Classical.choose
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property)
  else
    Classical.choose (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))

theorem shiftedKeyCorrectionWitness_mem
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (p : {p // p ∈ shiftedKeyRegularBadPrimes h x}) (i : Fin 2) :
    shiftedKeyCorrectionWitness h x hh0 hhEven p i ∈
      shiftedKeyCorrectionWitnesses h x := by
  by_cases hi : i = 0
  · simp only [shiftedKeyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))).1
  · simp only [shiftedKeyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))).2.1

theorem shiftedKeyCorrectionWitness_prime
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (p : {p // p ∈ shiftedKeyRegularBadPrimes h x}) (i : Fin 2) :
    shiftedKeyWitnessPrime h
      (shiftedKeyCorrectionWitness h x hh0 hhEven p i) = p := by
  by_cases hi : i = 0
  · simp only [shiftedKeyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))).2.2.2.1
  · simp only [shiftedKeyCorrectionWitness, hi, ↓reduceIte]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))).2.2.2.2

theorem shiftedKeyCorrectionWitness_ne
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (p : {p // p ∈ shiftedKeyRegularBadPrimes h x}) :
    shiftedKeyCorrectionWitness h x hh0 hhEven p 0 ≠
      shiftedKeyCorrectionWitness h x hh0 hhEven p 1 := by
  simpa [shiftedKeyCorrectionWitness] using
    (Classical.choose_spec (Classical.choose_spec
      (exists_two_shiftedKeyCorrectionWitnesses hh0 hhEven p.property))).2.2.1

theorem shiftedKeyCorrectionWitness_injective
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    Function.Injective fun z :
        {p // p ∈ shiftedKeyRegularBadPrimes h x} × Fin 2 =>
      (⟨shiftedKeyCorrectionWitness h x hh0 hhEven z.1 z.2,
        shiftedKeyCorrectionWitness_mem h x hh0 hhEven z.1 z.2⟩ :
          {w // w ∈ shiftedKeyCorrectionWitnesses h x}) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ heq
  have hpq : (p : ℕ) = q := by
    have hw :
        shiftedKeyCorrectionWitness h x hh0 hhEven p i =
          shiftedKeyCorrectionWitness h x hh0 hhEven q j :=
      congrArg Subtype.val heq
    have := congrArg (shiftedKeyWitnessPrime h) hw
    simpa only [shiftedKeyCorrectionWitness_prime] using this
  have hpqSubtype : p = q := Subtype.ext hpq
  subst q
  have hij : i = j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact (shiftedKeyCorrectionWitness_ne h x hh0 hhEven p
        (congrArg Subtype.val heq)).elim
    · exact (shiftedKeyCorrectionWitness_ne h x hh0 hhEven p
        (congrArg Subtype.val heq).symm).elim
    · rfl
  subst j
  rfl

theorem two_mul_shiftedKeyRegularBadPrimes_card_le
    (h x : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    2 * (shiftedKeyRegularBadPrimes h x).card ≤
      (shiftedKeyMidWitnesses h x).card +
        (shiftedKeyOmegaWitnesses h x).card := by
  let f := fun z :
      {p // p ∈ shiftedKeyRegularBadPrimes h x} × Fin 2 =>
    (⟨shiftedKeyCorrectionWitness h x hh0 hhEven z.1 z.2,
      shiftedKeyCorrectionWitness_mem h x hh0 hhEven z.1 z.2⟩ :
        {w // w ∈ shiftedKeyCorrectionWitnesses h x})
  have hcard := Fintype.card_le_of_injective f
    (shiftedKeyCorrectionWitness_injective h x hh0 hhEven)
  simpa [Fintype.card_prod, shiftedKeyCorrectionWitnesses_card,
    Nat.mul_comm] using hcard

noncomputable def shiftedKeySmallExceptionalPrimes (x : ℕ) : Finset ℕ :=
  keySmallExceptionalPrimes x

noncomputable def shiftedKeyEndpointExceptionalPrimes
    (h x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p => p = 2 ∨ x < p + h

noncomputable def shiftedKeyNonsquarefreeExceptionalPrimes
    (h x : ℕ) : Finset ℕ :=
  (shiftedKeySievedPrimes h x).filter fun p =>
    p ≠ 2 ∧ p + h ≤ x ∧ ¬Squarefree (p + h)

noncomputable def shiftedKeyRoughSquareWitness
    (h p : ℕ) : Σ _q : ℕ, ℕ :=
  let q := repeatedPrime (p + h)
  ⟨q, (p + h) / (q * q)⟩

theorem shiftedKeyRoughSquareWitness_mem
    {h x p : ℕ} (hhEven : Even h)
    (hp : p ∈ shiftedKeyNonsquarefreeExceptionalPrimes h x) :
    shiftedKeyRoughSquareWitness h p ∈ keyRoughSquareWitnesses x := by
  have hpData := Finset.mem_filter.mp hp
  have hpSieved := hpData.1
  have hpne := hpData.2.1
  have hnle := hpData.2.2.1
  have hnNot := hpData.2.2.2
  let q := repeatedPrime (p + h)
  have hqPrime : q.Prime := repeatedPrime_prime hnNot
  have hqSqDiv : q * q ∣ p + h := repeatedPrime_sq_dvd hnNot
  have hnpos : 0 < p + h := by
    have hpPrime := (Finset.mem_filter.mp hpSieved).2.1
    have hp0 : 0 < p := hpPrime.pos
    omega
  have hqSqLe : q * q ≤ p + h := Nat.le_of_dvd hnpos hqSqDiv
  have hqLe : q ≤ x := by
    have hqq : q ≤ q * q := by nlinarith [hqPrime.two_le]
    omega
  have hqLowerReal : (x : ℝ) ^ ((1 : ℝ) / 10) < q :=
    shiftedKeySieved_primeFactor_gt_threshold hhEven hpne hpSieved hqPrime
      ((show q ∣ q * q from ⟨q, rfl⟩).trans hqSqDiv)
  have hqLower :
      ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1 ≤ q := by
    have hfloor : ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ < q :=
      (Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).2 hqLowerReal
    omega
  unfold keyRoughSquareWitnesses shiftedKeyRoughSquareWitness
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hqLower, hqLe⟩, ?_⟩
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.div_pos hqSqLe (Nat.mul_pos hqPrime.pos hqPrime.pos)
  · exact (Nat.div_le_div_right hnle)

theorem shiftedKeyRoughSquareWitness_injective
    (h x : ℕ) :
    Set.InjOn (shiftedKeyRoughSquareWitness h)
      (shiftedKeyNonsquarefreeExceptionalPrimes h x) := by
  intro p hp r hr hpr
  have hpNot := (Finset.mem_filter.mp hp).2.2.2
  have hrNot := (Finset.mem_filter.mp hr).2.2.2
  have hpDiv := repeatedPrime_sq_dvd hpNot
  have hrDiv := repeatedPrime_sq_dvd hrNot
  have hpProd :
      repeatedPrime (p + h) * repeatedPrime (p + h) *
          ((p + h) /
            (repeatedPrime (p + h) * repeatedPrime (p + h))) = p + h :=
    Nat.mul_div_cancel' hpDiv
  have hrProd :
      repeatedPrime (r + h) * repeatedPrime (r + h) *
          ((r + h) /
            (repeatedPrime (r + h) * repeatedPrime (r + h))) = r + h :=
    Nat.mul_div_cancel' hrDiv
  have hnEq : p + h = r + h := by
    have := congrArg
      (fun z : Σ _q : ℕ, ℕ => z.1 * z.1 * z.2) hpr
    simpa only [shiftedKeyRoughSquareWitness, hpProd, hrProd] using this
  omega

theorem shiftedKeyNonsquarefreeExceptionalPrimes_card_le
    (h x : ℕ) (hhEven : Even h) :
    (shiftedKeyNonsquarefreeExceptionalPrimes h x).card ≤
      (keyRoughSquareWitnesses x).card := by
  let f := fun p :
      {p // p ∈ shiftedKeyNonsquarefreeExceptionalPrimes h x} =>
    (⟨shiftedKeyRoughSquareWitness h p,
      shiftedKeyRoughSquareWitness_mem hhEven p.property⟩ :
        {w // w ∈ keyRoughSquareWitnesses x})
  have hf : Function.Injective f := by
    intro p r heq
    apply Subtype.ext
    apply shiftedKeyRoughSquareWitness_injective h x p.property r.property
    exact congrArg Subtype.val heq
  simpa using Fintype.card_le_of_injective f hf

theorem shiftedKeyExceptionalPrimes_card_le_parts (h x : ℕ) :
    (shiftedKeyExceptionalPrimes h x).card ≤
      (shiftedKeySmallExceptionalPrimes x).card +
        (shiftedKeyEndpointExceptionalPrimes h x).card +
          (shiftedKeyNonsquarefreeExceptionalPrimes h x).card := by
  let U := shiftedKeySmallExceptionalPrimes x ∪
    shiftedKeyEndpointExceptionalPrimes h x ∪
      shiftedKeyNonsquarefreeExceptionalPrimes h x
  have hsub : shiftedKeyExceptionalPrimes h x ⊆ U := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpSieved := hpData.1
    have hpRange := (Finset.mem_filter.mp hpSieved).1
    rcases hpData.2 with hpTwo | hpSmall | hpEnd | hpNot
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      unfold shiftedKeyEndpointExceptionalPrimes
      exact Finset.mem_filter.mpr ⟨hpRange, Or.inl hpTwo⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      unfold shiftedKeySmallExceptionalPrimes keySmallExceptionalPrimes
      exact Finset.mem_filter.mpr ⟨hpRange, hpSmall⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      unfold shiftedKeyEndpointExceptionalPrimes
      exact Finset.mem_filter.mpr ⟨hpRange, Or.inr hpEnd⟩
    · by_cases hpTwo : p = 2
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        unfold shiftedKeyEndpointExceptionalPrimes
        exact Finset.mem_filter.mpr ⟨hpRange, Or.inl hpTwo⟩
      · by_cases hpEnd : x < p + h
        · apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          unfold shiftedKeyEndpointExceptionalPrimes
          exact Finset.mem_filter.mpr ⟨hpRange, Or.inr hpEnd⟩
        · apply Finset.mem_union.mpr
          right
          unfold shiftedKeyNonsquarefreeExceptionalPrimes
          exact Finset.mem_filter.mpr
            ⟨hpSieved, hpTwo, le_of_not_gt hpEnd, hpNot⟩
  calc
    (shiftedKeyExceptionalPrimes h x).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ (shiftedKeySmallExceptionalPrimes x).card +
        (shiftedKeyEndpointExceptionalPrimes h x).card +
          (shiftedKeyNonsquarefreeExceptionalPrimes h x).card := by
      dsimp only [U]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _)
          (shiftedKeyNonsquarefreeExceptionalPrimes h x).card)

theorem shiftedKeySmallExceptionalPrimes_card_real_le (x : ℕ) :
    ((shiftedKeySmallExceptionalPrimes x).card : ℝ) ≤
      (x : ℝ) ^ (0.9 : ℝ) + 1 := by
  exact keySmallExceptionalPrimes_card_real_le x

theorem shiftedKeyEndpointExceptionalPrimes_card_le (h x : ℕ) :
    (shiftedKeyEndpointExceptionalPrimes h x).card ≤ h + 1 := by
  let U : Finset ℕ := insert 2 (Finset.Icc (x + 1 - h) x)
  have hsub : shiftedKeyEndpointExceptionalPrimes h x ⊆ U := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hple : p ≤ x := by
      have := Finset.mem_range.mp hpData.1
      omega
    rcases hpData.2 with rfl | hpEnd
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_Icc.mpr
      constructor <;> omega
  calc
    (shiftedKeyEndpointExceptionalPrimes h x).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (x + 1 - h) x).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ h + 1 := by
      simp only [Nat.card_Icc]
      omega

/-- For fixed `h`, the extra endpoint interval `x < p+h` has bounded length;
together with the usual small and repeated-prime exceptions it is swallowed
by `x^0.91`. -/
theorem eventually_shiftedKeyExceptionalPrimes_card_le
    (h : ℕ) (hhEven : Even h) :
    ∀ᶠ x : ℕ in atTop,
      ((shiftedKeyExceptionalPrimes h x).card : ℝ) ≤
        (x : ℝ) ^ (0.91 : ℝ) := by
  have hrootReal :
      ∀ᶠ y : ℝ in atTop, 2 ≤ y ^ ((1 : ℝ) / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 2)
  have hroot := tendsto_natCast_atTop_atTop.eventually hrootReal
  have hbonusReal :
      ∀ᶠ y : ℝ in atTop, 5 ≤ y ^ (0.01 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).eventually
      (eventually_ge_atTop 5)
  have hbonus := tendsto_natCast_atTop_atTop.eventually hbonusReal
  have hhReal :
      ∀ᶠ y : ℝ in atTop, (h + 2 : ℕ) ≤ y ^ (0.9 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.9)).eventually
      (eventually_ge_atTop ((h + 2 : ℕ) : ℝ))
  have hhBound := tendsto_natCast_atTop_atTop.eventually hhReal
  filter_upwards [hroot, hbonus, hhBound,
      eventually_ge_atTop 1] with x hroot hbonus hhBound hx
  have hparts := shiftedKeyExceptionalPrimes_card_le_parts h x
  have hpartsReal :
      ((shiftedKeyExceptionalPrimes h x).card : ℝ) ≤
        (shiftedKeySmallExceptionalPrimes x).card +
          (shiftedKeyEndpointExceptionalPrimes h x).card +
            (shiftedKeyNonsquarefreeExceptionalPrimes h x).card := by
    exact_mod_cast hparts
  have hsmall := shiftedKeySmallExceptionalPrimes_card_real_le x
  have hend :
      ((shiftedKeyEndpointExceptionalPrimes h x).card : ℝ) ≤ h + 1 := by
    exact_mod_cast shiftedKeyEndpointExceptionalPrimes_card_le h x
  have hnonsquare :
      ((shiftedKeyNonsquarefreeExceptionalPrimes h x).card : ℝ) ≤
        2 * (x : ℝ) ^ (0.9 : ℝ) := by
    have hcard :=
      shiftedKeyNonsquarefreeExceptionalPrimes_card_le h x hhEven
    have hcardReal :
        ((shiftedKeyNonsquarefreeExceptionalPrimes h x).card : ℝ) ≤
          (keyRoughSquareWitnesses x).card := by
      exact_mod_cast hcard
    exact hcardReal.trans
      (keyRoughSquareWitnesses_card_real_le x (by simpa using hroot))
  have hxBase : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpowNineOne : (1 : ℝ) ≤ (x : ℝ) ^ (0.9 : ℝ) :=
    Real.one_le_rpow hxBase (by norm_num)
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans_le hxBase
  have hpow :
      (x : ℝ) ^ (0.01 : ℝ) * (x : ℝ) ^ (0.9 : ℝ) =
        (x : ℝ) ^ (0.91 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  calc
    ((shiftedKeyExceptionalPrimes h x).card : ℝ) ≤
        (shiftedKeySmallExceptionalPrimes x).card +
          (shiftedKeyEndpointExceptionalPrimes h x).card +
            (shiftedKeyNonsquarefreeExceptionalPrimes h x).card := hpartsReal
    _ ≤ ((x : ℝ) ^ (0.9 : ℝ) + 1) + (h + 1) +
          2 * (x : ℝ) ^ (0.9 : ℝ) := by gcongr
    _ ≤ 5 * (x : ℝ) ^ (0.9 : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one] at hhBound ⊢
      nlinarith
    _ ≤ (x : ℝ) ^ (0.01 : ℝ) * (x : ℝ) ^ (0.9 : ℝ) := by
      gcongr
    _ = (x : ℝ) ^ (0.91 : ℝ) := hpow

theorem shiftedChenCountCore_le_chenCountShift (h x : ℕ) :
    shiftedChenCountCore h x ≤ chenCountShift h x := by
  unfold shiftedChenCountCore chenCountShift
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨hpData.1, hpData.2.1, hpData.2.2.1⟩

/-- Fixed-shift combinatorial inequality (28), before replacing the core count
by the larger public counting function. -/
theorem shifted_key_inequality_core
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) -
          (shiftedSieveOmega h x : ℝ) / 2 -
            (x : ℝ) ^ (0.91 : ℝ) ≤
        (shiftedChenCountCore h x : ℝ) := by
  filter_upwards [eventually_shiftedKeyExceptionalPrimes_card_le h hhEven]
      with x hExceptional
  intro _hxEven
  have hPartition := shiftedKeySievedPrimes_card_le_partition h x
  have hWitness := two_mul_shiftedKeyRegularBadPrimes_card_le h x hh0 hhEven
  have hPartitionReal :
      ((shiftedKeySievedPrimes h x).card : ℝ) ≤
        (shiftedKeyChenPrimes h x).card +
          (shiftedKeyExceptionalPrimes h x).card +
            (shiftedKeyRegularBadPrimes h x).card := by
    exact_mod_cast hPartition
  have hWitnessReal :
      2 * ((shiftedKeyRegularBadPrimes h x).card : ℝ) ≤
        (shiftedKeyMidWitnesses h x).card +
          (shiftedKeyOmegaWitnesses h x).card := by
    exact_mod_cast hWitness
  rw [shiftedKeySievedPrimes_card, shiftedKeyChenPrimes_card] at hPartitionReal
  rw [shiftedKeyMidWitnesses_card, shiftedKeyOmegaWitnesses_card] at hWitnessReal
  push_cast at hPartitionReal hWitnessReal
  nlinarith

/-- Fixed-shift inequality (28) for `chenCountShift`. -/
theorem shifted_key_inequality
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) -
          (shiftedSieveOmega h x : ℝ) / 2 -
            (x : ℝ) ^ (0.91 : ℝ) ≤
        (chenCountShift h x : ℝ) := by
  filter_upwards [shifted_key_inequality_core h hh0 hhEven] with x hkey
  intro hxEven
  exact (hkey hxEven).trans (by
    exact_mod_cast shiftedChenCountCore_le_chenCountShift h x)

end Chen
