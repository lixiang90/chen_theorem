import ChenTheorem.Main.ShiftedLemma5
import ChenTheorem.Main.ShiftedLemma5Boundary
import ChenTheorem.Lemma5.Arithmetic

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! ### The shifted imprimitive-to-primitive character error -/

/-- Arithmetic majorant for the shifted `M₅` term.  The ambient summation
range is controlled by `x`, while the conductor displacement is measured
from the fixed residue `h`. -/
noncomputable def shiftedMFiveArithmeticMajorant
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ smoothedMIndices x q,
      ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d h (q.1 * q.2 * n)
          else 0)

theorem shiftedSieveModulus_decay_le_inv
    {h x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (hd : d ∈ shiftedSieveModuli h x ε) :
    (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) * (d : ℝ)⁻¹ := by
  have hddata := (Finset.mem_filter.mp hd).2
  have hdpos : 0 < d := by omega
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hdpow :
      (d : ℝ) ^ ((1 : ℝ) / 6) ≤
        (x : ℝ) ^ ((1 : ℝ) / 12) := by
    calc
      (d : ℝ) ^ ((1 : ℝ) / 6) ≤
          ((x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^
            ((1 : ℝ) / 6) :=
        Real.rpow_le_rpow (by positivity) hddata.2.2 (by norm_num)
      _ = (x : ℝ) ^ (((1 : ℝ) / 2 - ε) *
            ((1 : ℝ) / 6)) := by
        rw [← Real.rpow_mul (by positivity)]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
        apply Real.rpow_le_rpow_of_exponent_le hxone
        nlinarith
  rw [show -(5 : ℝ) / 6 = (1 : ℝ) / 6 + (-1) by ring,
    Real.rpow_add hdposR, Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_right hdpow (by positivity)

theorem shiftedModulus_conductor_gcd_sum_le
    {h x p a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hp : p.Prime) (ha : a ≠ 0) (hε : 0 ≤ ε) :
    ∑ d ∈ (shiftedSieveModuli h x ε).filter (p ∣ ·),
        (d : ℝ) ^ (-(5 : ℝ) / 6) *
          ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
            (Nat.gcd a k : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) *
        (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
          (a.divisors.card : ℝ) := by
  let D := (shiftedSieveModuli h x ε).filter (p ∣ ·)
  let K := Finset.Icc 1 x
  have hH : 0 ≤ (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    positivity
  have hdecay :
      ∀ d ∈ D,
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
          (x : ℝ) ^ ((1 : ℝ) / 12) * (d : ℝ)⁻¹ := by
    intro d hd
    exact shiftedSieveModulus_decay_le_inv hx1 hε
      (Finset.mem_filter.mp hd).1
  have hinnerExtend :
      ∀ d ∈ D,
        (d : ℝ)⁻¹ *
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) ≤
          ∑ k ∈ K,
            if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0 := by
    intro d hd
    have hdD := (Finset.mem_filter.mp hd).1
    have hddata := Finset.mem_filter.mp hdD
    have hdrange := Finset.mem_range.mp hddata.1
    have hdpos : 0 < d := by omega
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkd : k ∣ d := Nat.dvd_of_mem_divisors hk'.1
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkd hdpos
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        exact ⟨hkpos, (Nat.le_of_dvd hdpos hkd).trans (by omega)⟩
      · exact ⟨hkd, hk'.2⟩
    · intro k hkK hkdiv
      positivity
  have hfirst :
      ∑ d ∈ D,
          (d : ℝ) ^ (-(5 : ℝ) / 6) *
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ D,
            ∑ k ∈ K,
              if k ∣ d ∧ ¬p ∣ k then
                (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
              else 0 := by
    calc
      ∑ d ∈ D,
          (d : ℝ) ^ (-(5 : ℝ) / 6) *
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) ≤
        ∑ d ∈ D,
          ((x : ℝ) ^ ((1 : ℝ) / 12) * (d : ℝ)⁻¹) *
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_right (hdecay d hd) (by positivity)
      _ ≤ ∑ d ∈ D,
          (x : ℝ) ^ ((1 : ℝ) / 12) *
            ∑ k ∈ K,
              if k ∣ d ∧ ¬p ∣ k then
                (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
              else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (hinnerExtend d hd) (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ D,
            ∑ k ∈ K,
              if k ∣ d ∧ ¬p ∣ k then
                (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
              else 0 := by rw [Finset.mul_sum]
  have hmodulus :
      ∀ k ∈ K,
        ∑ d ∈ D,
            (if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0) ≤
          (p : ℝ)⁻¹ * (harmonic x : ℝ) *
            ((Nat.gcd a k : ℝ) / (k : ℝ)) := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    by_cases hpk : p ∣ k
    · simp [hpk]
      exact mul_nonneg
        (mul_nonneg (by positivity) hH)
        (div_nonneg (by positivity) (by positivity))
    · have hcop : p.Coprime k :=
        hp.coprime_iff_not_dvd.mpr hpk
      let S := D.filter (k ∣ ·)
      let T := (Finset.Icc 1 x).filter (p * k ∣ ·)
      have hST : S ⊆ T := by
        intro d hd
        have hdS := Finset.mem_filter.mp hd
        have hdD := Finset.mem_filter.mp hdS.1
        have hpd := hdD.2
        have hdmod := hdD.1
        have hddata := Finset.mem_filter.mp hdmod
        have hdrange := Finset.mem_range.mp hddata.1
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hddata.2.1, by omega⟩
        · exact hcop.mul_dvd_of_dvd_of_dvd hpd hdS.2
      have hrecip :
          ∑ d ∈ S, (d : ℝ)⁻¹ ≤
            (p * k : ℝ)⁻¹ * (harmonic x : ℝ) := by
        calc
          ∑ d ∈ S, (d : ℝ)⁻¹ ≤
              ∑ d ∈ T, (d : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hST
            intro d hdT hdS
            positivity
          _ = (p * k : ℝ)⁻¹ *
              ∑ j ∈ Finset.Icc 1 (x / (p * k)),
                (j : ℝ)⁻¹ := by
              dsimp [T]
              rw [sum_inv_multiples x (p * k)
                (mul_pos hp.pos hkpos), Nat.cast_mul]
          _ ≤ (p * k : ℝ)⁻¹ * (harmonic x : ℝ) :=
            mul_le_mul_of_nonneg_left
              (sum_Icc_inv_le_harmonic
                (Nat.div_le_self x (p * k))) (by positivity)
      calc
        ∑ d ∈ D,
            (if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0) =
          (∑ d ∈ S, (d : ℝ)⁻¹) *
            (Nat.gcd a k : ℝ) := by
              simp only [hpk, not_false_eq_true, and_true]
              rw [← Finset.sum_filter]
              change (∑ d ∈ S, (d : ℝ)⁻¹ *
                (Nat.gcd a k : ℝ)) = _
              rw [Finset.sum_mul]
        _ ≤ ((p * k : ℝ)⁻¹ * (harmonic x : ℝ)) *
            (Nat.gcd a k : ℝ) :=
          mul_le_mul_of_nonneg_right hrecip (by positivity)
        _ = (p : ℝ)⁻¹ * (harmonic x : ℝ) *
            ((Nat.gcd a k : ℝ) / (k : ℝ)) := by
          rw [mul_inv]
          field_simp
  have hdouble :
      ∑ d ∈ D,
          ∑ k ∈ K,
            (if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0) ≤
        (p : ℝ)⁻¹ * (harmonic x : ℝ) *
          ((a.divisors.card : ℝ) * (harmonic x : ℝ)) := by
    rw [Finset.sum_comm]
    calc
      ∑ k ∈ K,
          ∑ d ∈ D,
            (if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0) ≤
        ∑ k ∈ K,
          ((p : ℝ)⁻¹ * (harmonic x : ℝ) *
            ((Nat.gcd a k : ℝ) / (k : ℝ))) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hmodulus k hk
      _ = (p : ℝ)⁻¹ * (harmonic x : ℝ) *
          ∑ k ∈ K, (Nat.gcd a k : ℝ) / (k : ℝ) := by
            rw [Finset.mul_sum]
      _ ≤ (p : ℝ)⁻¹ * (harmonic x : ℝ) *
          ((a.divisors.card : ℝ) * (harmonic x : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (gcd_div_sum_le_card_divisors_mul_harmonic ha)
          (by positivity)
  change (∑ d ∈ D,
      (d : ℝ) ^ (-(5 : ℝ) / 6) *
        ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
          (Nat.gcd a k : ℝ)) ≤ _
  calc
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) *
        ∑ d ∈ D,
          ∑ k ∈ K,
            if k ∣ d ∧ ¬p ∣ k then
              (d : ℝ)⁻¹ * (Nat.gcd a k : ℝ)
            else 0 := hfirst
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) *
        ((p : ℝ)⁻¹ * (harmonic x : ℝ) *
          ((a.divisors.card : ℝ) * (harmonic x : ℝ))) :=
      mul_le_mul_of_nonneg_left hdouble (by positivity)
    _ = (x : ℝ) ^ ((1 : ℝ) / 12) *
        (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
          (a.divisors.card : ℝ) := by ring

theorem shiftedMFiveArithmetic_inner_le
    {h x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (q : ℕ × ℕ) (n : ℕ) :
    ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d h (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - h)).divisors.card : ℝ)) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, e, hp, he, hn⟩ := (isPrimePow_nat_iff n).mp hnpp
    subst n
    have hminfac : (p ^ e).minFac = p := by
      rw [Nat.pow_minFac he.ne', hp.minFac_eq]
    rw [hminfac]
    let a := Int.natAbs
      (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - h)
    have hbad : ∀ d : ℕ, ¬(p ^ e).Coprime d ↔ p ∣ d := by
      intro d
      rw [Nat.coprime_pow_left_iff he p d,
        hp.coprime_iff_not_dvd]
      tauto
    have hassoc :
        ∀ d : ℕ,
          primitiveAssociateMajorant d h
              (q.1 * q.2 * p ^ e) ≤
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) := by
      intro d
      exact primitiveAssociateMajorant_le_primeFilter
        hp he (by exact dvd_mul_left (p ^ e) (q.1 * q.2))
    calc
      ∑ d ∈ shiftedSieveModuli h x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            (if ¬(p ^ e).Coprime d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                primitiveAssociateMajorant d h
                  (q.1 * q.2 * p ^ e)
            else 0) ≤
        ∑ d ∈ shiftedSieveModuli h x ε,
          ((6 : ℝ) ^ (46656 : ℝ) *
              (d : ℝ) ^ (-(5 : ℝ) / 6)) *
            (if p ∣ d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ)
            else 0) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hpd : p ∣ d
          · rw [if_pos ((hbad d).2 hpd), if_pos hpd]
            exact mul_le_mul
              (sieveCoefficient_le_decay_uniform d)
              (mul_le_mul_of_nonneg_left (hassoc d)
                ArithmeticFunction.vonMangoldt_nonneg)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (primitiveAssociateMajorant_nonneg _ _ _))
              (mul_nonneg (by positivity)
                (Real.rpow_nonneg (by positivity) _))
          · simp [hpd, (hbad d).not.mpr hpd]
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ∑ d ∈ (shiftedSieveModuli h x ε).filter (p ∣ ·),
              (d : ℝ) ^ (-(5 : ℝ) / 6) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ) := by
          symm
          calc
            (6 : ℝ) ^ (46656 : ℝ) *
                ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ d ∈ (shiftedSieveModuli h x ε).filter (p ∣ ·),
                  (d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ) =
              ∑ d ∈ (shiftedSieveModuli h x ε).filter (p ∣ ·),
                (6 : ℝ) ^ (46656 : ℝ) *
                  ArithmeticFunction.vonMangoldt (p ^ e) *
                  ((d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ)) := by
                rw [Finset.mul_sum]
            _ = ∑ d ∈ shiftedSieveModuli h x ε,
                ((6 : ℝ) ^ (46656 : ℝ) *
                    (d : ℝ) ^ (-(5 : ℝ) / 6)) *
                  (if p ∣ d then
                    ArithmeticFunction.vonMangoldt (p ^ e) *
                      ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                        (Nat.gcd a k : ℝ)
                  else 0) := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hpd : p ∣ d
                · simp only [if_pos hpd]
                  ring
                · simp [hpd]
      _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) := by
          by_cases ha0 : a = 0
          · have heq : q.1 * q.2 * p ^ e = h := by
              have hz :
                  (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - h) = 0 := by
                exact Int.natAbs_eq_zero.mp (by
                  simpa only [a] using ha0)
              exact_mod_cast (sub_eq_zero.mp hz)
            have hph : p ∣ h := by
              rw [← heq]
              exact dvd_mul_of_dvd_right
                (dvd_pow_self p he.ne') (q.1 * q.2)
            have hDempty :
                (shiftedSieveModuli h x ε).filter (p ∣ ·) = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro d hd
              have hd' := Finset.mem_filter.mp hd
              have hddata := (Finset.mem_filter.mp hd'.1).2
              have hpone := Nat.eq_one_of_dvd_coprimes
                hddata.2.1 hd'.2 hph
              exact hp.ne_one hpone
            simp [hDempty, ha0]
          · exact mul_le_mul_of_nonneg_left
              (shiftedModulus_conductor_gcd_sum_le
                (h := h) hx1 hp ha0 hε)
              (mul_nonneg (by positivity)
                ArithmeticFunction.vonMangoldt_nonneg)
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) := rfl

theorem shiftedDisplacement_divisors_card_le
    {h m x : ℕ} (hhx : h ≤ x) (hmx : m ≤ x) :
    ((Int.natAbs ((m : ℤ) - h)).divisors.card : ℝ) ≤
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 24) := by
  let a := Int.natAbs ((m : ℤ) - h)
  by_cases ha0 : a = 0
  · simp only [a, ha0, Nat.divisors_zero, Finset.card_empty,
      Nat.cast_zero]
    exact mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  · have hcard := card_divisors_cast_le_rpow ha0
    have hale : a ≤ x := by
      by_cases hmh : m ≤ h
      · have haeq : a = h - m := by
          simpa only [a] using
            (Int.natAbs_natCast_sub_natCast_of_le hmh)
        rw [haeq]
        omega
      · have hhm : h ≤ m := le_of_not_ge hmh
        have haeq : a = m - h := by
          simpa only [a] using
            (Int.natAbs_natCast_sub_natCast_of_ge hhm)
        rw [haeq]
        omega
    have hpow :
        (a : ℝ) ^ ((1 : ℝ) / 24) ≤
          (x : ℝ) ^ ((1 : ℝ) / 24) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hale)
        (by norm_num)
    exact hcard.trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem shiftedMFiveArithmetic_inner_le_uniform
    {h x : ℕ} {ε : ℝ} (hhx : h ≤ x)
    (hx : 2 ≤ x) (hε : 0 ≤ ε)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    {n : ℕ} (hn : n ∈ smoothedMIndices x q) :
    ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d h (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hm : q.1 * q.2 * n ≤ x := smoothedMArgument_le hq hn
  have hdiv := shiftedDisplacement_divisors_card_le hhx hm
  calc
    ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d h (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - h)).divisors.card : ℝ)) :=
      shiftedMFiveArithmetic_inner_le hx1 hε q n
    _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
                (x : ℝ) ^ ((1 : ℝ) / 24))) := by
      gcongr
    _ = (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
      have hexp :
          (1 : ℝ) / 8 = (1 : ℝ) / 12 + (1 : ℝ) / 24 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring

theorem shiftedMFiveArithmeticMajorant_le_explicit
    {h x : ℕ} {ε : ℝ} (hhx : h ≤ x)
    (hx : 2 ≤ x) (hε : 0 ≤ ε) :
    shiftedMFiveArithmeticMajorant h x ε ≤
      9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
  let A : ℝ :=
    (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 8) *
          (harmonic x : ℝ) ^ 2
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hlogx : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hH : 0 ≤ (harmonic x : ℝ) := by
    exact_mod_cast (show 0 ≤ harmonic x by
      rw [harmonic]
      positivity)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _))
      (sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (by positivity) hlogx) hH
  have hsum :
      shiftedMFiveArithmeticMajorant h x ε ≤
        ((chenPairs x).card : ℝ) * A * B := by
    rw [shiftedMFiveArithmeticMajorant]
    calc
      ∑ q ∈ chenPairs x,
          ∑ n ∈ smoothedMIndices x q,
            ∑ d ∈ shiftedSieveModuli h x ε,
              (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                  (3 : ℝ) ^ distinctPrimeFactors d /
                    (Nat.totient d : ℝ)) *
                (if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d h (q.1 * q.2 * n)
                else 0) ≤
        ∑ q ∈ chenPairs x, A * B := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ∑ n ∈ smoothedMIndices x q,
                ∑ d ∈ shiftedSieveModuli h x ε,
                  (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                      (3 : ℝ) ^ distinctPrimeFactors d /
                        (Nat.totient d : ℝ)) *
                    (if ¬n.Coprime d then
                      ArithmeticFunction.vonMangoldt n *
                        primitiveAssociateMajorant d h
                          (q.1 * q.2 * n)
                    else 0) ≤
              ∑ n ∈ smoothedMIndices x q,
                A * (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
                    apply Finset.sum_le_sum
                    intro n hn
                    simpa only [A] using
                      shiftedMFiveArithmetic_inner_le_uniform
                        hhx hx hε hq hn
            _ = A * ∑ n ∈ smoothedMIndices x q,
                ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹ := by
                    rw [Finset.mul_sum]
            _ ≤ A * B := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        simpa only [B] using
                          sum_smoothedMIndices_vonMangoldt_div_minFac_le
                            hx q)
                      hA
      _ = ((chenPairs x).card : ℝ) * A * B := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcard := chenPairs_card_cast_le x hx1
  calc
    shiftedMFiveArithmeticMajorant h x ε ≤
        ((chenPairs x).card : ℝ) * A * B := hsum
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * A * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hA) hB
    _ = 9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
      have hexp :
          (23 : ℝ) / 24 = (5 : ℝ) / 6 + (1 : ℝ) / 8 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [A, B]
      ring

theorem shiftedMFiveArithmeticMajorant_le_fixed_rpow
    {h x : ℕ} {ε : ℝ} (hhx : h ≤ x)
    (hx : 2 ≤ x) (hε : 0 ≤ ε)
    (hlogOne : 1 ≤ Real.log (x : ℝ))
    (hlogFive :
      (Real.log x) ^ 5 ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    shiftedMFiveArithmeticMajorant h x ε ≤
      mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) := by
  let P : ℝ :=
    9 * (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((23 : ℝ) / 24)
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hxpos : 0 < (x : ℝ) := by positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    shiftedMFiveArithmeticMajorant h x ε ≤
        P * ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) ^ 3) := by
      simpa only [P, mul_assoc] using
        (shiftedMFiveArithmeticMajorant_le_explicit
          (h := h) (x := x) (ε := ε) hhx hx hε)
    _ ≤ P * (8 * K * (Real.log x) ^ 5) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [K] using mFive_log_loss_le hlogOne) hP0
    _ ≤ P * (8 * K *
        (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogFive
          (mul_nonneg (by norm_num) hK0)) hP0
    _ = mFivePowerConstant *
        (x : ℝ) ^ ((581 : ℝ) / 600) := by
      have hexp :
          (581 : ℝ) / 600 =
            (23 : ℝ) / 24 + (1 : ℝ) / 100 := by
        norm_num
      rw [mFivePowerConstant, hexp, Real.rpow_add hxpos]
      dsimp only [P, K]
      ring

theorem eventually_shiftedMFiveArithmeticMajorant_le_rpow
    (h : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      shiftedMFiveArithmeticMajorant h x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    eventually_ge_atTop 2, eventually_ge_atTop h] with
      x hlogFive hlogOne hx2 hhx
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  calc
    shiftedMFiveArithmeticMajorant h x ε ≤
        mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) :=
      shiftedMFiveArithmeticMajorant_le_fixed_rpow
        hhx hx2 hε0.le hlogOne hlogFive
    _ ≤ mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxone (by linarith))
        mFivePowerConstant_pos.le

theorem shiftedImprimitive_sub_primitive_eq_neg_bad
    {h x d : ℕ} (hd : 0 < d) (hhd : h.Coprime d) :
    shiftedImprimitiveCharacterContribution h x d -
        shiftedPrimitiveCharacterContribution h x d =
      -shiftedPrimitiveBadCharacterContribution h x d := by
  unfold shiftedImprimitiveCharacterContribution
    shiftedPrimitiveCharacterContribution
    shiftedPrimitiveBadCharacterContribution
  simp only [nontrivialCharSum, dif_neg hd.ne']
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχone : χ = 1
  · simp [hχone]
  simp only [hχone, ↓reduceIte]
  have hhcop : IsCoprime (h : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hhd
  have hhval := χ.primitiveCharacter_apply_of_isCoprime hhcop
  have hhstar :
      starRingEnd ℂ (χ (h : ZMod d)) =
        starRingEnd ℂ (χ.primitiveCharacter h) := by
    congr 1
    simpa only [Int.cast_natCast] using hhval.symm
  rw [hhstar, ← mul_sub, ← mul_neg]
  congr 1
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqcop : Nat.Coprime (q.1 * q.2) d
  · rw [if_pos hqcop, if_pos hqcop, if_pos hqcop]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hncop : n.Coprime d
    · rw [if_neg (not_not.mpr hncop), neg_zero]
      have hprod : (q.1 * q.2 * n).Coprime d :=
        Nat.Coprime.mul_left hqcop hncop
      have hprodZ : IsCoprime (q.1 * q.2 * n : ℤ) (d : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr hprod
      have hval := χ.primitiveCharacter_apply_of_isCoprime hprodZ
      have hval' :
          χ ((q.1 : ZMod d) * q.2 * n) =
            χ.primitiveCharacter (q.1 * q.2 * n) := by
        simpa only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul]
          using hval.symm
      rw [hval']
      ring
    · rw [if_pos hncop]
      have hnotprod : ¬(q.1 * q.2 * n).Coprime d := by
        intro hprod
        exact hncop (Nat.Coprime.of_dvd_left
          (by exact dvd_mul_left n (q.1 * q.2)) hprod)
      have hnonunit :
          ¬IsUnit ((q.1 * q.2 * n : ℕ) : ZMod d) := by
        intro hu
        exact hnotprod
          ((ZMod.isUnit_iff_coprime (q.1 * q.2 * n) d).1 hu)
      have hzero :
          χ ((q.1 * q.2 * n : ℕ) : ZMod d) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit
      have hzero' : χ ((q.1 : ZMod d) * q.2 * n) = 0 := by
        simpa using hzero
      rw [hzero', mul_zero, zero_sub, neg_eq_neg_one_mul]
  · rw [if_neg hqcop, if_neg hqcop, if_neg hqcop]
    simp

theorem shiftedMFive_eq_badContribution
    {h x : ℕ} {ε : ℝ} :
    shiftedMFive h x ε =
      ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          ‖shiftedPrimitiveBadCharacterContribution h x d‖ := by
  unfold shiftedMFive
  apply Finset.sum_congr rfl
  intro d hdmem
  have hddata := (Finset.mem_filter.mp hdmem).2
  have hdpos : 0 < d := by omega
  rw [shiftedImprimitive_sub_primitive_eq_neg_bad
    hdpos hddata.2.1.symm, norm_neg]

theorem shiftedPrimitiveBadCharacterContribution_eq_sum
    {h x d : ℕ} (hd : 0 < d) :
    shiftedPrimitiveBadCharacterContribution h x d =
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
          (smoothedMKernel x q n : ℂ) *
            nontrivialCharSum d (fun χ =>
              starRingEnd ℂ (χ.primitiveCharacter h) *
                χ.primitiveCharacter (q.1 * q.2 * n)) := by
  unfold shiftedPrimitiveBadCharacterContribution
  have hfun :
      (fun χ : DirichletCharacter ℂ d =>
        starRingEnd ℂ (χ.primitiveCharacter h) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ (smoothedMIndices x q).filter
                (fun n => ¬n.Coprime d),
              (smoothedMKernel x q n : ℂ) *
                χ.primitiveCharacter (q.1 * q.2 * n)) =
        fun χ =>
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ (smoothedMIndices x q).filter
                (fun n => ¬n.Coprime d),
              (smoothedMKernel x q n : ℂ) *
                (starRingEnd ℂ (χ.primitiveCharacter h) *
                  χ.primitiveCharacter (q.1 * q.2 * n)) := by
    funext χ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfun]
  rw [nontrivialCharSum_sum_comm hd.ne'
    ((chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) d))
    (fun χ q =>
      ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
        (smoothedMKernel x q n : ℂ) *
          (starRingEnd ℂ (χ.primitiveCharacter h) *
            χ.primitiveCharacter (q.1 * q.2 * n)))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [nontrivialCharSum_sum_comm hd.ne'
    ((smoothedMIndices x q).filter (fun n => ¬n.Coprime d))
    (fun χ n =>
      (smoothedMKernel x q n : ℂ) *
        (starRingEnd ℂ (χ.primitiveCharacter h) *
          χ.primitiveCharacter (q.1 * q.2 * n)))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [nontrivialCharSum_const_mul hd.ne']

theorem shiftedPrimitiveBadCharacterContribution_norm_le_of
    {h x d : ℕ} (hd : 0 < d) (hx : Real.exp 3 ≤ (x : ℝ))
    (B : ℕ → ℝ)
    (hB : ∀ m : ℕ,
      ‖nontrivialCharSum d (fun χ =>
        starRingEnd ℂ (χ.primitiveCharacter h) *
          χ.primitiveCharacter m)‖ ≤ B m) :
    ‖shiftedPrimitiveBadCharacterContribution h x d‖ ≤
      primitiveBadMajorant x d B := by
  rw [shiftedPrimitiveBadCharacterContribution_eq_sum hd,
    primitiveBadMajorant]
  refine norm_bisum_mul_le
    ((chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) d))
    (fun q =>
      (smoothedMIndices x q).filter (fun n => ¬n.Coprime d))
    (fun q n => (smoothedMKernel x q n : ℂ))
    (fun q n =>
      nontrivialCharSum d (fun χ =>
        starRingEnd ℂ (χ.primitiveCharacter h) *
          χ.primitiveCharacter (q.1 * q.2 * n)))
    (fun _q n => ArithmeticFunction.vonMangoldt n)
    (fun q n => B (q.1 * q.2 * n)) ?_ ?_ ?_
  · intro q hq n hn
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_smoothedMKernel_le_vonMangoldt hx
      (Finset.mem_filter.mp hq).1
  · intro q hq n hn
    simpa only [Nat.cast_mul] using hB (q.1 * q.2 * n)
  · intro q hq n hn
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem shiftedPrimitiveBadCharacterContribution_norm_le
    {h x d : ℕ} (hd : 0 < d) (hdsq : Squarefree d)
    (hodd : Odd d) (hhd : h.Coprime d)
    (hx : Real.exp 3 ≤ (x : ℝ)) :
    ‖shiftedPrimitiveBadCharacterContribution h x d‖ ≤
      primitiveBadMajorant x d
        (fun m => primitiveAssociateMajorant d h m) := by
  apply shiftedPrimitiveBadCharacterContribution_norm_le_of hd hx
  intro m
  exact nontrivial_primitiveAssociateSum_norm_le_majorant
    hd hdsq hodd hhd

theorem shiftedMFive_le_primitiveBadMajorant
    {h x : ℕ} {ε : ℝ} (hh : Even h)
    (hx : Real.exp 3 ≤ (x : ℝ)) :
    shiftedMFive h x ε ≤
      ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          primitiveBadMajorant x d
            (fun m => primitiveAssociateMajorant d h m) := by
  rw [shiftedMFive_eq_badContribution]
  apply Finset.sum_le_sum
  intro d hdmem
  have hddata := (Finset.mem_filter.mp hdmem).2
  have hdpos : 0 < d := by omega
  by_cases hdsq : Squarefree d
  · have hdodd : Odd d :=
      (Nat.Coprime.of_dvd_right hh.two_dvd hddata.2.1).odd_of_right
    have hbound :=
      shiftedPrimitiveBadCharacterContribution_norm_le
        hdpos hdsq hdodd hddata.2.1.symm hx
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
    norm_num

theorem shiftedMFive_le_arithmeticMajorant
    {h x : ℕ} {ε : ℝ} (hh : Even h)
    (hx : Real.exp 3 ≤ (x : ℝ)) :
    shiftedMFive h x ε ≤
      shiftedMFiveArithmeticMajorant h x ε := by
  calc
    shiftedMFive h x ε ≤
        ∑ d ∈ shiftedSieveModuli h x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            primitiveBadMajorant x d
              (fun m => primitiveAssociateMajorant d h m) :=
      shiftedMFive_le_primitiveBadMajorant hh hx
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            ∑ q ∈ (chenPairs x).filter
                (fun q => Nat.Coprime (q.1 * q.2) d),
              ∑ n ∈ (smoothedMIndices x q).filter
                  (fun n => ¬n.Coprime d),
                ArithmeticFunction.vonMangoldt n *
                  primitiveAssociateMajorant d h
                    (q.1 * q.2 * n) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primitiveBadMajorant]
    _ ≤ ∑ d ∈ shiftedSieveModuli h x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d h
                      (q.1 * q.2 * n)
                else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · calc
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ (smoothedMIndices x q).filter
                (fun n => ¬n.Coprime d),
              ArithmeticFunction.vonMangoldt n *
                primitiveAssociateMajorant d h
                  (q.1 * q.2 * n) =
            ∑ q ∈ (chenPairs x).filter
                (fun q => Nat.Coprime (q.1 * q.2) d),
              ∑ n ∈ smoothedMIndices x q,
                if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d h
                      (q.1 * q.2 * n)
                else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Finset.sum_filter]
          _ ≤ ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d h
                      (q.1 * q.2 * n)
                else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _)
              intro q hq hq'
              apply Finset.sum_nonneg
              intro n hn
              by_cases hbad : ¬n.Coprime d
              · rw [if_pos hbad]
                exact mul_nonneg
                  ArithmeticFunction.vonMangoldt_nonneg
                  (primitiveAssociateMajorant_nonneg _ _ _)
              · rw [if_neg hbad]
      · positivity
    _ = shiftedMFiveArithmeticMajorant h x ε := by
      rw [shiftedMFiveArithmeticMajorant]
      calc
        (∑ d ∈ shiftedSieveModuli h x ε,
            (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                (3 : ℝ) ^ distinctPrimeFactors d /
                  (Nat.totient d : ℝ)) *
              ∑ q ∈ chenPairs x,
                ∑ n ∈ smoothedMIndices x q,
                  if ¬n.Coprime d then
                    ArithmeticFunction.vonMangoldt n *
                      primitiveAssociateMajorant d h
                        (q.1 * q.2 * n)
                  else 0) =
          ∑ d ∈ shiftedSieveModuli h x ε,
            ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                    (3 : ℝ) ^ distinctPrimeFactors d /
                      (Nat.totient d : ℝ)) *
                  (if ¬n.Coprime d then
                    ArithmeticFunction.vonMangoldt n *
                      primitiveAssociateMajorant d h
                        (q.1 * q.2 * n)
                  else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
        _ = ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              ∑ d ∈ shiftedSieveModuli h x ε,
                (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                    (3 : ℝ) ^ distinctPrimeFactors d /
                      (Nat.totient d : ℝ)) *
                  (if ¬n.Coprime d then
                    ArithmeticFunction.vonMangoldt n *
                      primitiveAssociateMajorant d h
                        (q.1 * q.2 * n)
                  else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]

theorem eventually_shiftedMFive_le_rpow
    {h : ℕ} (hh : Even h) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      shiftedMFive h x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards
      [eventually_shiftedMFiveArithmeticMajorant_le_rpow h hε0 hε1,
        hxlargeEventually] with x hmajor hxlarge
  exact (shiftedMFive_le_arithmeticMajorant hh hxlarge).trans hmajor

theorem shiftedSmoothedSieveExpansion_power_bound
    (h : ℕ) (hh : Even h) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      shiftedSmoothedSieveExpansion h x ε ≤
        shiftedMOne h x ε + shiftedMTwo h x ε +
          C * (x : ℝ) ^ (1 - ε / 3) := by
  obtain ⟨C₃, hC₃, hthree⟩ :=
    abs_shiftedMThree_power_bound hh hε0 hε1
  let C : ℝ := C₃ + mFivePowerConstant
  refine ⟨C, add_pos hC₃ mFivePowerConstant_pos, ?_⟩
  filter_upwards [hthree,
    eventually_shiftedMFive_le_rpow hh hε0 hε1,
    eventually_ge_atTop 1] with x hthree hfive hx1
  have hsmooth :=
    shiftedSmoothedSieveExpansion_le hh hx1 hε0.le
  have hfour := shiftedMFour_le_shiftedMTwo_add_shiftedMFive h x ε
  calc
    shiftedSmoothedSieveExpansion h x ε ≤
        shiftedMOne h x ε + |shiftedMThree h x ε| +
          shiftedMFour h x ε := hsmooth
    _ ≤ shiftedMOne h x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (shiftedMTwo h x ε + shiftedMFive h x ε) := by
      gcongr
    _ ≤ shiftedMOne h x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (shiftedMTwo h x ε +
            mFivePowerConstant *
              (x : ℝ) ^ (1 - ε / 3)) := by
      gcongr
    _ = shiftedMOne h x ε + shiftedMTwo h x ε +
        C * (x : ℝ) ^ (1 - ε / 3) := by
      dsimp only [C]
      ring

/-! ### Assembly of the full shifted Lemma 5 -/

theorem one_sub_mul_shiftedSieveOmega_le_shiftedSieveM_add_smallTail
    {h x : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) :
    (1 - ε) * (shiftedSieveOmega h x : ℝ) ≤
      shiftedSieveM h x + (shiftedSieveMSmallTail h x ε : ℝ) := by
  simp only [shiftedSieveOmega, shiftedSieveM,
    shiftedSieveMSmallTail, Nat.cast_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hY : 1 < Y := by simpa only [Y] using one_lt_pairQuotient hq
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hsubset :
      shiftedOmegaThirdPrimes h x q ⊆ shiftedSieveMIndices h x q := by
    intro p hp
    simp only [shiftedOmegaThirdPrimes, Finset.mem_filter,
      Finset.mem_range] at hp
    simp only [shiftedSieveMIndices, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩
  have hΛsum :
      ∑ p ∈ shiftedOmegaThirdPrimes h x q,
          ArithmeticFunction.vonMangoldt p ≤
        ∑ n ∈ shiftedSieveMIndices h x q,
          ArithmeticFunction.vonMangoldt n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  calc
    (1 - ε) * (shiftedOmegaThirdPrimes h x q).card =
        ∑ p ∈ shiftedOmegaThirdPrimes h x q, (1 - ε) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ p ∈ shiftedOmegaThirdPrimes h x q,
        ((Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt p +
          if (p : ℝ) < Y ^ (1 - ε) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata :
          p.Prime ∧ (p : ℝ) ≤ Y ∧
            shiftedRough h x (q.1 * q.2 * p) := by
        have hp' := hp
        simp only [shiftedOmegaThirdPrimes, Finset.mem_filter,
          Finset.mem_range] at hp'
        simpa only [Y] using hp'.2
      have hw0 :
          0 ≤ (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt p :=
        mul_nonneg (le_of_lt (inv_pos.mpr hlogY))
          ArithmeticFunction.vonMangoldt_nonneg
      by_cases hsmall : (p : ℝ) < Y ^ (1 - ε)
      · simp only [hsmall, ↓reduceIte]
        linarith
      · simp only [hsmall, ↓reduceIte, add_zero]
        have hpow : Y ^ (1 - ε) ≤ (p : ℝ) := le_of_not_gt hsmall
        have hlogpow :
            Real.log (Y ^ (1 - ε)) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hpow
        rw [Real.log_rpow hY0] at hlogpow
        have hdiv :
            1 - ε ≤ Real.log (p : ℝ) / Real.log Y :=
          (le_div_iff₀ hlogY).2 (by simpa [mul_comm] using hlogpow)
        simpa [ArithmeticFunction.vonMangoldt_apply_prime hpdata.1,
          div_eq_mul_inv, mul_comm] using hdiv
    _ = (Real.log Y)⁻¹ *
          (∑ p ∈ shiftedOmegaThirdPrimes h x q,
            ArithmeticFunction.vonMangoldt p) +
        (shiftedOmegaSmallThirdPrimes h x ε q).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [shiftedOmegaSmallThirdPrimes, Y]
    _ ≤ (Real.log Y)⁻¹ *
          (∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n) +
        (shiftedOmegaSmallThirdPrimes h x ε q).card := by
      gcongr
    _ = (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n +
        (shiftedOmegaSmallThirdPrimes h x ε q).card := by
      rfl

theorem shiftedSieveOmega_le_of_shiftedSieveM_le
    {h x : ℕ} {ε E_M E_tail : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hM : shiftedSieveM h x ≤
      shiftedMOne h x ε + shiftedMTwo h x ε + E_M)
    (htail : (shiftedSieveMSmallTail h x ε : ℝ) ≤ E_tail) :
    (shiftedSieveOmega h x : ℝ) ≤
      (shiftedMOne h x ε + shiftedMTwo h x ε + E_M + E_tail) /
        (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε1)).2
  have hbase :=
    one_sub_mul_shiftedSieveOmega_le_shiftedSieveM_add_smallTail
      (h := h) (x := x) hε0
  linarith

theorem shiftedSieveMSmallTail_le_log
    (h : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (shiftedSieveMSmallTail h x ε : ℝ) ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_shiftedSieveMSmallTail_le_rpow h hε0
      (hε1.trans (by norm_num)),
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 12) (r := (2.01 : ℝ)) (by positivity)] with
      x htail hpower
  exact htail.trans (by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 2)))

theorem shiftedSieveM_le_mOne_add_mTwo
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      shiftedSieveM h x ≤
        shiftedMOne h x ε + shiftedMTwo h x ε +
          C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_smooth, hC_smooth, hsmoothing⟩ :=
    eventually_shiftedSieveMSmoothingError_le h hh0 hhEven
  obtain ⟨C_power, hC_power, hexpansion⟩ :=
    shiftedSmoothedSieveExpansion_power_bound h hhEven ε hε0 hε1
  let C : ℝ := C_smooth + C_power
  refine ⟨C, add_pos hC_smooth hC_power, ?_⟩
  filter_upwards [hsmoothing, hexpansion,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 3) (r := (2.01 : ℝ)) (by positivity),
    eventually_gt_atTop 1] with
      x hsmoothing hexpansion hpower hx1
  have hformula :=
    shiftedSieveM_le_smoothedSieveExpansion_add_smoothingError
      (h := h) (ε := ε) hx1 hε0.le
        (hε1.le.trans (by norm_num))
  have hpower' :
      C_power * (x : ℝ) ^ (1 - ε / 3) ≤
        C_power * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower hC_power.le)
  calc
    shiftedSieveM h x ≤
        shiftedSmoothedSieveExpansion h x ε +
          shiftedSieveMSmoothingError h x := hformula
    _ ≤ (shiftedMOne h x ε + shiftedMTwo h x ε +
          C_power * (x : ℝ) ^ (1 - ε / 3)) +
        C_smooth * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
      gcongr
    _ ≤ (shiftedMOne h x ε + shiftedMTwo h x ε +
          C_power * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ)) +
        C_smooth * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
      gcongr
    _ = shiftedMOne h x ε + shiftedMTwo h x ε +
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

/-- Fixed-shift analogue of Chen's Lemma 5. -/
theorem shiftedSieveOmega_le_mOne_add_mTwo
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (shiftedSieveOmega h x : ℝ) ≤
        (shiftedMOne h x ε + shiftedMTwo h x ε) / (1 - ε) +
          C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_M, hC_M, hM⟩ :=
    shiftedSieveM_le_mOne_add_mTwo h hh0 hhEven ε hε0 hε1
  obtain ⟨C_tail, hC_tail, htail⟩ :=
    shiftedSieveMSmallTail_le_log h ε hε0 hε1
  let C := (C_M + C_tail) / (1 - ε)
  have hεlt1 : ε < 1 := hε1.trans (by norm_num)
  have hden : 0 < 1 - ε := sub_pos.mpr hεlt1
  refine ⟨C, div_pos (add_pos hC_M hC_tail) hden, ?_⟩
  filter_upwards [hM, htail] with x hxM hxtail
  have hbound :=
    shiftedSieveOmega_le_of_shiftedSieveM_le hε0.le hεlt1
      hxM hxtail
  calc
    (shiftedSieveOmega h x : ℝ) ≤
        (shiftedMOne h x ε + shiftedMTwo h x ε +
            C_M * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) +
            C_tail * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ)) /
          (1 - ε) := hbound
    _ = (shiftedMOne h x ε + shiftedMTwo h x ε) / (1 - ε) +
          C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      field_simp
      ring

end Chen
