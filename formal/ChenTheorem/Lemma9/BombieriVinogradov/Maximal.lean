import ChenTheorem.Lemma9.BombieriVinogradov.Bilinear

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# A maximal dyadic large-sieve layer

The Type-I and Type-II hyperbola sums have an upper endpoint depending on the
other variable.  This file begins the standard Rademacher--Menshov reduction:
an arbitrary prefix of an interval of length `2^L` is controlled by a
recursively defined dyadic energy with only an `L + 1` loss.  The recursive
form avoids choosing and bookkeeping an explicit list of binary blocks.
-/

/-- Sum of squared norms over the dyadic blocks needed by the recursive
prefix decomposition.  At level `L+1`, the full left half is recorded and the
construction recurses into both halves. -/
noncomputable def dyadicPrefixEnergy (f : ℕ → ℂ) : ℕ → ℕ → ℝ
  | M, 0 => ‖∑ n ∈ Finset.Ioc M (M + 1), f n‖ ^ 2
  | M, L + 1 =>
      ‖∑ n ∈ Finset.Ioc M (M + 2 ^ L), f n‖ ^ 2 +
        dyadicPrefixEnergy f M L +
          dyadicPrefixEnergy f (M + 2 ^ L) L

theorem dyadicPrefixEnergy_nonneg
    (f : ℕ → ℂ) (M L : ℕ) :
    0 ≤ dyadicPrefixEnergy f M L := by
  induction L generalizing M with
  | zero =>
      rw [dyadicPrefixEnergy]
      positivity
  | succ L ih =>
      rw [dyadicPrefixEnergy]
      exact add_nonneg
        (add_nonneg (sq_nonneg _) (ih M))
        (ih (M + 2 ^ L))

/-- Weighted two-term Cauchy inequality in the exact form needed by the
dyadic induction. -/
theorem norm_add_sq_le_weighted
    (z w : ℂ) (r : ℝ) (hr : 0 < r) :
    ‖z + w‖ ^ 2 ≤
      (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 := by
  have htri : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hsquare :
      ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hid :
      (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 -
          (‖z‖ + ‖w‖) ^ 2 =
        (r * ‖z‖ - ‖w‖) ^ 2 / r := by
    field_simp [hr.ne']
    ring
  have hweighted :
      (‖z‖ + ‖w‖) ^ 2 ≤
        (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 := by
    apply sub_nonneg.mp
    rw [hid]
    exact div_nonneg (sq_nonneg _) hr.le
  exact hsquare.trans hweighted

/-- Every prefix of a `2^L`-long interval is bounded by `L+1` times the
dyadic energy.  This is the finite Rademacher--Menshov inequality that will
turn the ordinary character large sieve into a maximal one. -/
theorem norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
    (f : ℕ → ℂ) (M L K : ℕ) (hK : K ≤ 2 ^ L) :
    ‖∑ n ∈ Finset.Ioc M (M + K), f n‖ ^ 2 ≤
      ((L + 1 : ℕ) : ℝ) * dyadicPrefixEnergy f M L := by
  induction L generalizing M K with
  | zero =>
      have hK01 : K = 0 ∨ K = 1 := by omega
      rcases hK01 with rfl | rfl
      · simp [dyadicPrefixEnergy]
      · simp [dyadicPrefixEnergy]
  | succ L ih =>
      let H : ℕ := 2 ^ L
      have hpow : 2 ^ (L + 1) = H + H := by
        dsimp only [H]
        rw [pow_succ]
        omega
      have hKfull : K ≤ H + H := by
        simpa [hpow] using hK
      by_cases hleft : K ≤ H
      · have hbase := ih M K hleft
        have hEleft : 0 ≤ dyadicPrefixEnergy f M L :=
          dyadicPrefixEnergy_nonneg f M L
        have hEright :
            0 ≤ dyadicPrefixEnergy f (M + H) L :=
          dyadicPrefixEnergy_nonneg f (M + H) L
        have hblock :
            0 ≤ ‖∑ n ∈ Finset.Ioc M (M + H), f n‖ ^ 2 := by
          positivity
        rw [dyadicPrefixEnergy]
        dsimp only [H] at hbase hEright ⊢
        have hcoef :
            ((L + 1 : ℕ) : ℝ) ≤ ((L + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (L + 1)
        have hsum :
            dyadicPrefixEnergy f M L ≤
              ‖∑ n ∈ Finset.Ioc M (M + 2 ^ L), f n‖ ^ 2 +
                dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L := by
          linarith
        exact hbase.trans
          (mul_le_mul hcoef hsum hEleft (by positivity))
      · have hHK : H ≤ K := by omega
        let K' : ℕ := K - H
        have hK' : K' ≤ H := by
          dsimp only [K']
          omega
        have hend : M + K = (M + H) + K' := by
          dsimp only [K']
          omega
        let A : ℂ := ∑ n ∈ Finset.Ioc M (M + H), f n
        let B : ℂ := ∑ n ∈ Finset.Ioc (M + H) ((M + H) + K'), f n
        have hsplit :
            (∑ n ∈ Finset.Ioc M (M + K), f n) = A + B := by
          rw [hend]
          dsimp only [A, B]
          exact (Finset.sum_Ioc_consecutive f
            (Nat.le_add_right M H)
            (Nat.le_add_right (M + H) K')).symm
        have hB := ih (M + H) K' hK'
        have hr : (0 : ℝ) < L + 1 := by positivity
        have hweighted := norm_add_sq_le_weighted A B (L + 1) hr
        have hEleft : 0 ≤ dyadicPrefixEnergy f M L :=
          dyadicPrefixEnergy_nonneg f M L
        have hEright :
            0 ≤ dyadicPrefixEnergy f (M + H) L :=
          dyadicPrefixEnergy_nonneg f (M + H) L
        rw [hsplit]
        rw [dyadicPrefixEnergy]
        dsimp only [H] at A B hweighted hB hEright ⊢
        calc
          ‖A + B‖ ^ 2 ≤
              (((L : ℝ) + 1) + 1) * ‖A‖ ^ 2 +
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hweighted
          _ ≤ (((L : ℝ) + 1) + 1) * ‖A‖ ^ 2 +
                (((L : ℝ) + 1) + 1) *
                  dyadicPrefixEnergy f (M + 2 ^ L) L := by
            have hterm :
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 ≤
                  (((L : ℝ) + 1) + 1) *
                    dyadicPrefixEnergy f (M + 2 ^ L) L := by
              calc
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 ≤
                    (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) *
                      (((L : ℝ) + 1) *
                        dyadicPrefixEnergy f (M + 2 ^ L) L) := by
                  apply mul_le_mul_of_nonneg_left
                  · simpa only [Nat.cast_add, Nat.cast_one] using hB
                  · positivity
                _ = (((L : ℝ) + 1) + 1) *
                      dyadicPrefixEnergy f (M + 2 ^ L) L := by
                  field_simp
            linarith
          _ ≤ (((L : ℝ) + 1) + 1) *
                (‖A‖ ^ 2 + dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L) := by
            nlinarith [sq_nonneg ‖A‖]
          _ = (((L + 1 + 1 : ℕ) : ℝ)) *
                (‖A‖ ^ 2 + dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L) := by
            push_cast
            ring

/-- Primitive-character average of the dyadic energy on one conductor
interval. -/
noncomputable def dyadicCharacterEnergyMean
    (D Q M L : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i *
      dyadicPrefixEnergy (fun n => a n * i.2 n) M L

theorem dyadicCharacterEnergyMean_nonneg
    (D Q M L : ℕ) (a : ℕ → ℂ) :
    0 ≤ dyadicCharacterEnergyMean D Q M L a := by
  rw [dyadicCharacterEnergyMean]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i)
      (dyadicPrefixEnergy_nonneg _ M L)

/-- A fixed prefix second moment is controlled by the averaged dyadic
energy.  The next theorem bounds that energy by repeated applications of the
ordinary dyadic character large sieve. -/
theorem characterPrefixSecondMoment_le_dyadicCharacterEnergyMean
    (D Q M L K : ℕ) (a : ℕ → ℂ) (hK : K ≤ 2 ^ L) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M K a i.2‖ ^ 2) ≤
      ((L + 1 : ℕ) : ℝ) * dyadicCharacterEnergyMean D Q M L a := by
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M K a i.2‖ ^ 2) ≤
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            (((L + 1 : ℕ) : ℝ) *
              dyadicPrefixEnergy (fun n => a n * i.2 n) M L) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _
        (primitiveDyadicWeight_nonneg i)
      simpa only [characterIntervalSum] using
        norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
          (fun n => a n * i.2 n) M L K hK
    _ = ((L + 1 : ℕ) : ℝ) *
        dyadicCharacterEnergyMean D Q M L a := by
      rw [dyadicCharacterEnergyMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem dyadicCharacterEnergyMean_succ
    (D Q M L : ℕ) (a : ℕ → ℂ) :
    dyadicCharacterEnergyMean D Q M (L + 1) a =
      (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M (2 ^ L) a i.2‖ ^ 2) +
        dyadicCharacterEnergyMean D Q M L a +
          dyadicCharacterEnergyMean D Q (M + 2 ^ L) L a := by
  rw [dyadicCharacterEnergyMean, dyadicCharacterEnergyMean,
    dyadicCharacterEnergyMean]
  simp_rw [dyadicPrefixEnergy, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rfl

/-- Repeated use of the ordinary dyadic character large sieve bounds the
entire recursive energy with one further logarithmic loss. -/
theorem dyadicCharacterEnergyMean_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M L : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        dyadicCharacterEnergyMean D Q M L a ≤
          C * ((L + 1 : ℕ) : ℝ) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
  rcases characterIntervalSecondMoment_dyadic_le with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M L a hD hDQ
  induction L generalizing M with
  | zero =>
      have hbase := hlarge D Q M 1 a hD hDQ
      simpa [dyadicCharacterEnergyMean, dyadicPrefixEnergy,
        characterIntervalSum] using hbase
  | succ L ih =>
      let H : ℕ := 2 ^ L
      have hpow : 2 ^ (L + 1) = H + H := by
        dsimp only [H]
        rw [pow_succ]
        omega
      have hDpos : (0 : ℝ) < D := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
      let Sleft : ℝ :=
        ∑ n ∈ Finset.Ioc M (M + H), ‖a n‖ ^ 2
      let Sright : ℝ :=
        ∑ n ∈ Finset.Ioc (M + H) ((M + H) + H), ‖a n‖ ^ 2
      have hSleft : 0 ≤ Sleft := by
        dsimp only [Sleft]
        positivity
      have hSright : 0 ≤ Sright := by
        dsimp only [Sright]
        positivity
      let G : ℝ := C * ((Q : ℝ) + ((H + H : ℕ) : ℝ) / (D : ℝ))
      have hG : 0 ≤ G := by
        dsimp only [G]
        positivity
      have hfactor :
          C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) ≤ G := by
        dsimp only [G]
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact add_le_add_right
          (div_le_div_of_nonneg_right
            (by exact_mod_cast Nat.le_add_right H H) hDpos.le) _
      have hblock := hlarge D Q M H a hD hDQ
      have hblock' :
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M H a i.2‖ ^ 2) ≤
            G * Sleft := by
        calc
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M H a i.2‖ ^ 2) ≤
              C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft := by
            simpa only [Sleft] using hblock
          _ ≤ G * Sleft :=
            mul_le_mul_of_nonneg_right hfactor hSleft
      have hleft := ih M
      have hright := ih (M + H)
      have hleft' :
          dyadicCharacterEnergyMean D Q M L a ≤
            (((L + 1 : ℕ) : ℝ) * G) * Sleft := by
        calc
          dyadicCharacterEnergyMean D Q M L a ≤
              C * ((L + 1 : ℕ) : ℝ) *
                ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft := by
            simpa only [H, Sleft] using hleft
          _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sleft := by
            have hcoef :
                ((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ))) ≤
                  ((L + 1 : ℕ) : ℝ) * G :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            calc
              C * ((L + 1 : ℕ) : ℝ) *
                  ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft =
                  (((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)))) * Sleft := by ring
              _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sleft :=
                mul_le_mul_of_nonneg_right hcoef hSleft
      have hright' :
          dyadicCharacterEnergyMean D Q (M + H) L a ≤
            (((L + 1 : ℕ) : ℝ) * G) * Sright := by
        calc
          dyadicCharacterEnergyMean D Q (M + H) L a ≤
              C * ((L + 1 : ℕ) : ℝ) *
                ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sright := by
            simpa only [H, Sright, Nat.add_assoc] using hright
          _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sright := by
            have hcoef :
                ((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ))) ≤
                  ((L + 1 : ℕ) : ℝ) * G :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            calc
              C * ((L + 1 : ℕ) : ℝ) *
                  ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sright =
                  (((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)))) * Sright := by ring
              _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sright :=
                mul_le_mul_of_nonneg_right hcoef hSright
      have hsum :
          Sleft + Sright =
            ∑ n ∈ Finset.Ioc M (M + 2 ^ (L + 1)), ‖a n‖ ^ 2 := by
        dsimp only [Sleft, Sright]
        rw [hpow]
        simpa [Nat.add_assoc] using
          Finset.sum_Ioc_consecutive (fun n => ‖a n‖ ^ 2)
            (Nat.le_add_right M H) (Nat.le_add_right (M + H) H)
      rw [dyadicCharacterEnergyMean_succ]
      calc
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M (2 ^ L) a i.2‖ ^ 2) +
            dyadicCharacterEnergyMean D Q M L a +
              dyadicCharacterEnergyMean D Q (M + 2 ^ L) L a ≤
            G * Sleft + (((L + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 : ℕ) : ℝ) * G) * Sright := by
          exact add_le_add (add_le_add hblock' hleft') hright'
        _ = (((L + 1 + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 : ℕ) : ℝ) * G) * Sright := by
          push_cast
          ring
        _ ≤ (((L + 1 + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 + 1 : ℕ) : ℝ) * G) * Sright := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by exact_mod_cast Nat.le_succ (L + 1)) hG)
              hSright) _
        _ = C * ((L + 1 + 1 : ℕ) : ℝ) *
              ((Q : ℝ) + ((2 ^ (L + 1) : ℕ) : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + 2 ^ (L + 1)), ‖a n‖ ^ 2 := by
          rw [← hsum]
          dsimp only [G]
          rw [hpow]
          ring

/-- The largest squared character prefix sum among the first `N` terms.
The range is `N + 1`, so the zero-length prefix is included and the indexing
finset is always nonempty. -/
noncomputable def maxCharacterPrefixSq {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Finset.range (N + 1)).sup' (by simp)
    (fun K => ‖characterIntervalSum M K a χ‖ ^ 2)

theorem characterIntervalSum_sq_le_maxCharacterPrefixSq {q : ℕ}
    (M N K : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hK : K ≤ N) :
    ‖characterIntervalSum M K a χ‖ ^ 2 ≤
      maxCharacterPrefixSq M N a χ := by
  rw [maxCharacterPrefixSq]
  exact Finset.le_sup'
    (fun J => (‖characterIntervalSum M J a χ‖ ^ 2 : ℝ))
    (Finset.mem_range.2 (Nat.lt_succ_iff.2 hK))

theorem maxCharacterPrefixSq_nonneg {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    0 ≤ maxCharacterPrefixSq M N a χ := by
  exact (sq_nonneg ‖characterIntervalSum M 0 a χ‖).trans
    (characterIntervalSum_sq_le_maxCharacterPrefixSq M N 0 a χ
      (Nat.zero_le N))

/-- Pointwise Rademacher--Menshov bound for the maximum over all prefixes of
length at most `N`, where `N` is contained in a dyadic interval of level
`L`. -/
theorem maxCharacterPrefixSq_le_dyadicPrefixEnergy {q : ℕ}
    (M N L : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hN : N ≤ 2 ^ L) :
    maxCharacterPrefixSq M N a χ ≤
      ((L + 1 : ℕ) : ℝ) *
        dyadicPrefixEnergy (fun n => a n * χ n) M L := by
  rw [maxCharacterPrefixSq]
  apply Finset.sup'_le
  intro K hK
  have hKN : K ≤ N := by
    exact Nat.le_of_lt_succ (Finset.mem_range.1 hK)
  simpa only [characterIntervalSum] using
    norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
      (fun n => a n * χ n) M L K (hKN.trans hN)

/-- Maximal dyadic character large sieve.  Each character may choose its own
prefix length; the price compared with the ordinary large sieve is only the
square of the dyadic depth. -/
theorem maxCharacterPrefixSecondMoment_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N L : ℕ) (a : ℕ → ℂ),
        1 ≤ D → D ≤ Q → N ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                maxCharacterPrefixSq M N a i.2) ≤
            C * (((L + 1 : ℕ) : ℝ) ^ 2) *
              ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
  rcases dyadicCharacterEnergyMean_le with ⟨C, hC, henergy⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N L a hD hDQ hN
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * maxCharacterPrefixSq M N a i.2) ≤
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            (((L + 1 : ℕ) : ℝ) *
              dyadicPrefixEnergy (fun n => a n * i.2 n) M L) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (maxCharacterPrefixSq_le_dyadicPrefixEnergy M N L a i.2 hN)
        (primitiveDyadicWeight_nonneg i)
    _ = ((L + 1 : ℕ) : ℝ) *
          dyadicCharacterEnergyMean D Q M L a := by
      rw [dyadicCharacterEnergyMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ((L + 1 : ℕ) : ℝ) *
          (C * ((L + 1 : ℕ) : ℝ) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (henergy D Q M L a hD hDQ) (by positivity)
    _ = C * (((L + 1 : ℕ) : ℝ) ^ 2) *
          ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
      ring

/-- Dyadic bilinear large sieve with a character-dependent endpoint in the
second factor.  The square root turns `maxCharacterPrefixSq` back into the
norm of a maximal prefix, while keeping the weighted Cauchy--Schwarz step
entirely over nonnegative real quantities. -/
theorem maximalBilinearCharacterMean_dyadic_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (D Q M R K N L : ℕ) (a b : ℕ → ℂ),
        1 ≤ D → D ≤ Q → N ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M R a i.2‖ *
                  Real.sqrt (maxCharacterPrefixSq K N b i.2)) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (R : ℝ) / (D : ℝ)) *
                ∑ m ∈ Finset.Ioc M (M + R), ‖a m‖ ^ 2) *
              (C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
                ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                  ∑ n ∈ Finset.Ioc K (K + 2 ^ L), ‖b n‖ ^ 2) := by
  rcases characterIntervalSecondMoment_dyadic_le with
    ⟨C₀, hC₀, hinterval⟩
  rcases maxCharacterPrefixSecondMoment_dyadic_le with
    ⟨C₁, hC₁, hmax⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro D Q M R K N L a b hD hDQ hN
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun i => ‖characterIntervalSum M R a i.2‖)
    (fun i => Real.sqrt (maxCharacterPrefixSq K N b i.2))
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact hinterval D Q M R a hD hDQ
  · calc
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            Real.sqrt (maxCharacterPrefixSq K N b i.2) ^ 2) =
          ∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              maxCharacterPrefixSq K N b i.2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.sq_sqrt (maxCharacterPrefixSq_nonneg K N b i.2)]
      _ ≤ C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc K (K + 2 ^ L), ‖b n‖ ^ 2 :=
        hmax D Q K N L b hD hDQ hN
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg
      (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun m _ => sq_nonneg _)

end Chen.BombieriVinogradov
