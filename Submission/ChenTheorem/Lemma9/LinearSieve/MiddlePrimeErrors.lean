import Submission.ChenTheorem.Lemma9.LinearSieve.PrimeSubsequence

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- A modulus made from small sifting primes and one larger prime has a
unique such decomposition. -/
theorem middlePrime_product_injective (P K : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hK : ∀ k ∈ K, Nat.Prime k)
    (hsep : ∀ p ∈ P, ∀ k ∈ K, p < k) :
    Set.InjOn (fun kd : ℕ × ℕ => kd.2 * kd.1)
      (↑(K ×ˢ (∏ p ∈ P, p).divisors) : Set (ℕ × ℕ)) := by
  rintro ⟨k, d⟩ hkd ⟨k', d'⟩ hk'd' heq
  obtain ⟨hk, hd⟩ := mem_product.mp hkd
  obtain ⟨hk', hd'⟩ := mem_product.mp hk'd'
  dsimp only at heq
  have hkdiv : k ∣ d' * k' := heq ▸ (dvd_mul_left k d)
  have hkk : k = k' := by
    rcases (hK k hk).dvd_mul.mp hkdiv with hkd' | hkk'
    · have hkP := hkd'.trans (Nat.mem_divisors.mp hd').1
      obtain ⟨p, hp, hkp⟩ := ((hK k hk).prime.dvd_finsetProd_iff id).mp hkP
      have hkp' : k = p := (Nat.prime_dvd_prime_iff_eq (hK k hk) (hP p hp)).mp hkp
      have := hsep p hp k hk
      omega
    · exact (Nat.prime_dvd_prime_iff_eq (hK k hk) (hK k' hk')).mp hkk'
  subst k'
  have hdd : d = d' := Nat.eq_of_mul_eq_mul_right (hK k hk).pos heq
  exact Prod.ext rfl hdd

/-- Summing actual middle-prime remainder moduli has multiplicity one.
The divisor support is essential: replacing it by all `d ≤ Q/k` would
lose this property. -/
theorem sum_middlePrime_errors_le (P K : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hK : ∀ k ∈ K, Nat.Prime k)
    (hsep : ∀ p ∈ P, ∀ k ∈ K, p < k)
    (Q : ℕ) (E : ℕ → ℝ) (hE : ∀ d, 0 ≤ E d) :
    (∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d * k ≤ Q, E (d * k)) ≤
      ∑ m ∈ Icc 1 Q, E m := by
  let T := (K ×ˢ (∏ p ∈ P, p).divisors).filter (fun kd => kd.2 * kd.1 ≤ Q)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, a.2 * a.1 = b.2 * b.1 → a = b := by
    intro a ha b hb
    exact middlePrime_product_injective P K hP hK hsep
      (mem_filter.mp ha).1 (mem_filter.mp hb).1
  have hsub : T.image (fun kd => kd.2 * kd.1) ⊆ Icc 1 Q := by
    intro m hm
    obtain ⟨⟨k, d⟩, hkd, rfl⟩ := mem_image.mp hm
    obtain ⟨hmem, hQ⟩ := mem_filter.mp hkd
    obtain ⟨hk, hd⟩ := mem_product.mp hmem
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact mem_Icc.mpr ⟨Nat.mul_pos hdpos (hK k hk).pos, hQ⟩
  calc
    _ = ∑ kd ∈ T, E (kd.2 * kd.1) := by
      simp only [T, sum_filter, sum_product]
    _ = ∑ m ∈ T.image (fun kd => kd.2 * kd.1), E m := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hE m)

open Filter in
/-- BV controls the total middle-prime remainder sum without an extra
divisor weight. Both prime sets may vary with the main parameter `x`. -/
theorem eventually_middlePrime_errors_le
    (hBV : BombieriVinogradov.Statement) (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B →
        ∀ P K : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → (∀ k ∈ K, Nat.Prime k) →
        (∀ p ∈ P, ∀ k ∈ K, p < k) →
        (∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d * k ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) x) ≤
            C * x / (Real.log x) ^ A := by
  obtain ⟨B, C, hB, hC, herr⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) A hA
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [herr] with x hx
  intro Q hQ P K hP hK hsep
  exact (sum_middlePrime_errors_le P K hP hK hsep Q
    (fun d => BombieriVinogradov.reducedThetaError x d x)
    (fun d => BombieriVinogradov.reducedThetaError_nonneg x d x)).trans (hx Q hQ (fun _ => x))

end Chen.LinearSieve
