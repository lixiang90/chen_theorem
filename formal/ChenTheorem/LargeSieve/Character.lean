/-
The character form of the large sieve (inequality (2) of Chen's paper) and its
dyadic corollary (inequality (3)), following the paper's derivation from the
additive form (4):

For a primitive character `χ` mod `q`, the Gauss sum expansion
`τ(χ̄) χ(n) = ∑ₐ χ̄(a) e(na/q)` with `|τ(χ̄)|² = q` gives
`(q/φ(q)) ∑*_{χ} |T(χ)|² ≤ ∑_{(a,q)=1} |S(a/q)|²`, and summing over `q ≤ X`
against the additive large sieve (`Additive.lean`) yields
`∑_{q≤X} (q/φ(q)) ∑*_{χ mod q} |∑_{M<n≤M+N} aₙ χ(n)|² ≤ (X² + πN) ∑|aₙ|²`.

The proof of `|τ(χ)|² = q` for primitive `χ` is the standard one through the
same expansion and finite Parseval on `ZMod q`, included here since Mathlib
does not yet have it.
-/
import ChenTheorem.LargeSieve.Additive
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.SimpleRing.Principal

open Set MeasureTheory intervalIntegral Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace Chen.LargeSieve

noncomputable local instance (p : Prop) : Decidable p := Classical.dec p

variable {q : ℕ} [NeZero q] {a : ℕ → ℂ} {s : Finset ℕ}

/-- `Ŝ(b) = ∑_{n ∈ s} aₙ e(nb/q)`, viewed as a function on `ZMod q`. -/
noncomputable def hatSum (b : ZMod q) : ℂ :=
  ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b)

/-- `Ŝ` evaluated at a lift agrees with the trigonometric sum at `b/q`. -/
lemma hatSum_eq_trigSum (b : ZMod q) :
    hatSum (a := a) (s := s) b = trigSum a s (b.val / q) := by
  rw [hatSum, trigSum]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hbval : (b.val : ZMod q) = b := by
    simpa only [ZMod.cast_id] using (ZMod.natCast_val (R := ZMod q) b)
  have hcast : (n * b : ZMod q) = ((n * b.val : ℤ) : ZMod q) := by
    calc
      (n : ZMod q) * b = (n : ZMod q) * (b.val : ZMod q) :=
        congrArg (fun z : ZMod q => (n : ZMod q) * z) hbval.symm
      _ = ((n * b.val : ℕ) : ZMod q) := by rw [Nat.cast_mul]
      _ = ((n * b.val : ℤ) : ZMod q) := by norm_cast
  rw [hcast, ZMod.stdAddChar_coe, fexp]
  push_cast
  ring_nf

/-- The Gauss-sum expansion `τ(χ̄) T(χ) = ∑_b χ̄(b) Ŝ(b)` for primitive `χ`. -/
lemma gaussSum_mul_charSum {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ s, a n * χ n) =
      ∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b := by
  have hprim : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
      ← DirichletCharacter.isPrimitive_def]
  rw [Finset.mul_sum]
  have key : ∀ n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar * (a n * χ n) =
      a n * ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
    intro n
    have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hprim (n : ZMod q)
    rw [inv_inv] at h
    have hgs : gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) =
        ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
      rw [gaussSum]
      exact Finset.sum_congr rfl fun b _ => by rw [AddChar.mulShift_apply]
    rw [hgs] at h
    calc
      gaussSum χ⁻¹ ZMod.stdAddChar * (a n * χ n) =
          a n * (χ n * gaussSum χ⁻¹ ZMod.stdAddChar) := by ring
      _ = a n * ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
        rw [← h]
  rw [Finset.sum_congr rfl fun n _ => key n]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hatSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Dirichlet character values at units have norm `1`. -/
lemma char_value_norm_one {χ : DirichletCharacter ℂ q} {u : (ZMod q)ˣ} :
    ‖χ (u : ZMod q)‖ = 1 := by
  have h1 : χ (u : ZMod q) ^ q.totient = 1 := by
    have h2 : ((u : ZMod q) ^ q.totient) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]
    rw [← map_pow, h2, map_one]
  have h3 : ‖χ (u : ZMod q)‖ ^ q.totient = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    ((Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne')).mp h3

/-- `‖χ n‖² = 1` at units and `0` otherwise. -/
lemma char_norm_sq (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    ‖χ n‖ ^ 2 = if IsUnit n then (1 : ℝ) else 0 := by
  by_cases hn : IsUnit n
  · rw [if_pos hn]
    obtain ⟨u, hu⟩ := hn
    rw [← hu, char_value_norm_one, one_pow]
  · rw [if_neg hn, MulChar.map_nonunit _ hn, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-- The number of units of `ZMod q` as a real sum. -/
lemma card_units_eq_totient :
    (Finset.univ.filter (fun n : ZMod q => IsUnit n)).card = q.totient := by
  have h1 : Fintype.card (ZMod q)ˣ = q.totient := ZMod.card_units_eq_totient q
  rw [← h1]
  rw [← Finset.card_univ]
  symm
  apply Finset.card_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
    (t := Finset.univ.filter (fun n : ZMod q => IsUnit n)) (fun u _ => (u : ZMod q))
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
  · intro u v _ _ h
    exact Units.ext h
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hx⟩ := hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, Finset.mem_univ _, hu⟩

/-- `∑_{n : ZMod q} ‖χ n‖² = φ(q)`. -/
lemma sum_char_norm_sq (χ : DirichletCharacter ℂ q) :
    (∑ n : ZMod q, ‖χ n‖ ^ 2) = (q.totient : ℝ) := by
  rw [Finset.sum_congr rfl fun n _ => char_norm_sq χ n, Finset.sum_boole,
    card_units_eq_totient]

/-- `star (stdAddChar x) = stdAddChar (-x)`. -/
lemma star_stdAddChar (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hnorm : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have h1 : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left h2).trans (eq_inv_of_mul_eq_one_left h1).symm

/-- The orthogonality of the standard additive character on `ZMod q`:
`∑_{n} e(nt) = q·δ_{t,0}`. -/
lemma sum_stdAddChar_mul (t : ZMod q) :
    (∑ n : ZMod q, ZMod.stdAddChar (n * t)) = if t = 0 then (q : ℂ) else 0 := by
  by_cases ht : t = 0
  · rw [ht, if_pos rfl]
    simp [mul_zero, AddChar.map_zero_eq_one]
  · rw [if_neg ht]
    have h2 : ZMod.stdAddChar.mulShift t ≠ 1 := by
      exact ZMod.isPrimitive_stdAddChar q ht
    have h4 : (∑ n : ZMod q, ZMod.stdAddChar (n * t)) =
        ∑ n : ZMod q, (ZMod.stdAddChar.mulShift t) n := by
      exact Finset.sum_congr rfl fun n _ => by
        rw [AddChar.mulShift_apply, mul_comm]
    rw [h4, AddChar.sum_eq_zero_of_ne_one h2]

/-- The double-sum identity underlying `|τ|² = q` and the character form of the
large sieve: `∑_n (∑_b z_b e(nb))·star(∑_c z_c e(nc)) = q ∑_b z_b·star(z_b)`
for complex `z` supported on... — here stated for `z_b = χ b`, in which case
the right-hand side is `q·φ(q)`. -/
lemma double_sum_stdAddChar (z : ZMod q → ℂ) :
    (∑ n : ZMod q, (∑ b : ZMod q, z b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, z c * ZMod.stdAddChar (n * c))) =
      (q : ℂ) * ∑ b : ZMod q, z b * star (z b) := by
  have h1 : ∀ n : ZMod q, (∑ b : ZMod q, z b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, z c * ZMod.stdAddChar (n * c)) =
      ∑ b : ZMod q, ∑ c : ZMod q, (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := by
    intro n
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [star_mul, star_stdAddChar]
    have hadd : ZMod.stdAddChar (n * b) * ZMod.stdAddChar (-(n * c)) =
        ZMod.stdAddChar (n * (b - c)) := by
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    calc
      z b * ZMod.stdAddChar (n * b) * (ZMod.stdAddChar (-(n * c)) * star (z c)) =
          (z b * star (z c)) *
            (ZMod.stdAddChar (n * b) * ZMod.stdAddChar (-(n * c))) := by ring
      _ = (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := by rw [hadd]
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ n : ZMod q, ∑ c : ZMod q,
        (z b * star (z c)) * ZMod.stdAddChar (n * (b - c))) =
        ∑ c : ZMod q, ∑ n : ZMod q,
          (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := Finset.sum_comm
    _ = ∑ c : ZMod q, (z b * star (z c)) *
        (if b - c = 0 then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_sum, sum_stdAddChar_mul]
    _ = (q : ℂ) * (z b * star (z b)) := by
      rw [Finset.sum_eq_single b]
      · simp [mul_comm]
      · intro c _ hcb
        simp [sub_ne_zero.mpr hcb.symm]
      · simp

/-- The Gauss-sum expansion for primitive `χ`: `χ̄(n)·τ(χ) = ∑_b χ(b) e(nb/q)`. -/
lemma char_inv_mul_gaussSum {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b) := by
  have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ n
  rw [← h, gaussSum]
  exact Finset.sum_congr rfl fun b _ => by rw [AddChar.mulShift_apply]

/-- `|τ(χ)|² = q` for primitive `χ` mod `q`. -/
lemma gaussSum_normSq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  set τ := gaussSum χ ZMod.stdAddChar with hτ
  have hexp := char_inv_mul_gaussSum hχ
  -- Way 1: `∑_n ‖χ⁻¹ n·τ‖² = φ(q)·‖τ‖²`.
  have h1 : (∑ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2) = (q.totient : ℝ) * ‖τ‖ ^ 2 := by
    have hn : ∀ n : ZMod q, ‖χ⁻¹ n‖ ^ 2 = if IsUnit n then (1 : ℝ) else 0 := by
      intro n
      exact char_norm_sq χ⁻¹ n
    rw [Finset.sum_congr rfl fun n _ => by rw [norm_mul, mul_pow, hn n], ← Finset.sum_mul,
      Finset.sum_boole, card_units_eq_totient]
  -- Way 2: `∑_n ‖χ⁻¹ n·τ‖² = q·φ(q)` via the double-sum identity.
  have h2c : (∑ n : ZMod q, (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, χ c * ZMod.stdAddChar (n * c))) = ((q * q.totient : ℝ) : ℂ) := by
    rw [double_sum_stdAddChar (fun b => χ b)]
    have h3 : (∑ b : ZMod q, χ b * star (χ b)) = ((q.totient : ℝ) : ℂ) := by
      have h4 : ∀ b : ZMod q, χ b * star (χ b) = ((‖χ b‖ ^ 2 : ℝ) : ℂ) := by
        intro b
        rw [show star (χ b) = conj (χ b) from rfl, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      rw [Finset.sum_congr rfl (fun b _ => h4 b), ← Complex.ofReal_sum, sum_char_norm_sq χ]
    rw [h3]
    push_cast
    ring
  have h2 : (∑ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2) = (q : ℝ) * q.totient := by
    have hnorm : ∀ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2 =
        ((∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
          star (∑ c : ZMod q, χ c * ZMod.stdAddChar (n * c))).re := by
      intro n
      rw [hτ, hexp n, ← Complex.normSq_eq_norm_sq]
      change Complex.normSq (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) =
        ((∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
          conj (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b))).re
      rw [Complex.mul_conj, Complex.ofReal_re]
    rw [Finset.sum_congr rfl fun n _ => hnorm n, ← Complex.re_sum, h2c, Complex.ofReal_re]
  have htot' : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hmul := h1.symm.trans h2
  exact mul_right_cancel₀ htot' (by simpa [mul_comm] using hmul)

/-- The orthogonality sum `∑_χ χ⁻¹(b)·star(χ⁻¹(c))` collapse helper:
`star (χ⁻¹ c) = χ c`. -/
lemma star_inv_char (χ : DirichletCharacter ℂ q) (c : ZMod q) :
    star (χ⁻¹ c) = χ c := by
  by_cases hc : IsUnit c
  · obtain ⟨u, hu⟩ := hc
    rw [← hu, MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
    have h1 : star ((χ (u : ZMod q))⁻¹) = χ (u : ZMod q) := by
      have h2 : star (χ (u : ZMod q)) = (χ (u : ZMod q))⁻¹ := by
        have hn := char_value_norm_one (χ := χ) (u := u)
        have h3 : (χ (u : ZMod q)) * star (χ (u : ZMod q)) = 1 := by
          change χ (u : ZMod q) * conj (χ (u : ZMod q)) = 1
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
            Complex.ofReal_one]
        exact eq_inv_of_mul_eq_one_right h3
      calc
        star ((χ (u : ZMod q))⁻¹) = (star (χ (u : ZMod q)))⁻¹ := by
          exact map_inv₀ (starRingEnd ℂ) _
        _ = ((χ (u : ZMod q))⁻¹)⁻¹ := by rw [h2]
        _ = χ (u : ZMod q) := inv_inv _
    exact h1
  · rw [MulChar.map_nonunit _ hc, MulChar.map_nonunit _ hc, star_zero]

/-- `∑_χ χ⁻¹(b)·χ(c) = φ(q)` if `b = c` is a unit, else `0`. -/
lemma sum_char_inv_mul_char (b c : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c) =
      if (b = c ∧ IsUnit b) then (q.totient : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · have h1 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = χ (b⁻¹ * c) := by
      intro χ
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
      have h2 : χ (b⁻¹) * χ b = 1 := by
        rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]
      change (χ b)⁻¹ * χ c = χ (b⁻¹ * c)
      rw [← eq_inv_of_mul_eq_one_left h2, ← map_mul]
    rw [Finset.sum_congr rfl (fun χ _ => h1 χ), DirichletCharacter.sum_characters_eq]
    have hd : b⁻¹ * c = 1 ↔ b = c := by
      constructor
      · intro h
        calc
          b = b * (b⁻¹ * c) := by rw [h, mul_one]
          _ = (b * b⁻¹) * c := by ring
          _ = c := by rw [ZMod.mul_inv_of_unit b hb, one_mul]
      · rintro rfl
        exact ZMod.inv_mul_of_unit b hb
    by_cases hbc : b = c
    · rw [if_pos (hd.mpr hbc), if_pos ⟨hbc, hb⟩]
    · rw [if_neg (fun h => hbc (hd.mp h)), if_neg (fun h => hbc h.1)]
  · rw [if_neg (fun h => hb h.2), Finset.sum_eq_zero]
    intro χ _
    rw [MulChar.map_nonunit _ hb, zero_mul]

/-- The character-form orthogonality identity:
`∑_χ ‖∑_b χ⁻¹(b) Ŝ(b)‖² = φ(q)·∑_{b unit} ‖Ŝ(b)‖²`. -/
lemma sum_all_char_hatSum :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2) =
      (q.totient : ℝ) * ∑ b : ZMod q,
        (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
  let H : ZMod q → ℂ := fun b => hatSum (a := a) (s := s) b
  change (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * H b‖ ^ 2) =
    (q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖H b‖ ^ 2 else 0)
  have h1c : (∑ χ : DirichletCharacter ℂ q,
      (∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c)) =
      ((q.totient : ℝ) : ℂ) * ∑ b : ZMod q,
        (if IsUnit b then (H b * star (H b)) else 0) := by
    have hstep : ∀ χ : DirichletCharacter ℂ q,
        (∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c) =
        ∑ b : ZMod q, ∑ c : ZMod q, (H b * star (H c)) * (χ⁻¹ b * star (χ⁻¹ c)) := by
      intro χ
      rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [star_mul, star_inv_char]
      ring
    rw [Finset.sum_congr rfl (fun χ _ => hstep χ), Finset.sum_comm,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    simp_rw [star_inv_char]
    calc
      (∑ c : ZMod q, ∑ χ : DirichletCharacter ℂ q,
          H b * star (H c) * (χ⁻¹ b * χ c)) =
          ∑ c : ZMod q, (H b * star (H c)) *
            (if b = c ∧ IsUnit b then (q.totient : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.mul_sum, sum_char_inv_mul_char b c]
      _ = (q.totient : ℂ) *
          (if IsUnit b then H b * star (H b) else 0) := by
        by_cases hb : IsUnit b
        · rw [if_pos hb, Finset.sum_eq_single b]
          · simp [hb, mul_comm]
          · intro c _ hcb
            simp [Ne.symm hcb, hb]
          · simp
        · simp [hb]
  have hnorm : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ b : ZMod q, χ⁻¹ b * H b‖ ^ 2 =
      ((∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c)).re := by
    intro χ
    rw [← Complex.normSq_eq_norm_sq]
    change Complex.normSq (∑ b : ZMod q, χ⁻¹ b * H b) =
      ((∑ b : ZMod q, χ⁻¹ b * H b) *
        conj (∑ b : ZMod q, χ⁻¹ b * H b)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
  have hY : (∑ b : ZMod q, (if IsUnit b then (H b * star (H b)) else 0)) =
      ((∑ b : ZMod q, (if IsUnit b then (‖H b‖ ^ 2 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : IsUnit b
    · rw [if_pos hb, if_pos hb, show star (H b) = conj (H b) from rfl,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [if_neg hb, if_neg hb, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl (fun χ _ => hnorm χ), ← Complex.re_sum, h1c, hY, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- The sum of `‖Ŝ(b)‖²` over units of `ZMod q` equals the sum of `‖S(b/q)‖²`
over reduced residues `1 ≤ b ≤ q`, `(b,q) = 1`. -/
lemma sum_units_hatSum_eq :
    (∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0)) =
      ∑ b ∈ (Finset.range q).filter (·.Coprime q), ‖trigSum a s (b / q)‖ ^ 2 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (s := Finset.univ.filter (fun b : ZMod q => IsUnit b))
    (t := (Finset.range q).filter (·.Coprime q)) (fun b _ => b.val)
  · intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : b.val.Coprime q := by
      exact (ZMod.isUnit_iff_coprime b.val q).mp (by simpa using hb.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt b), h1⟩
  · intro b₁ _ b₂ _ h
    exact ZMod.val_injective q h
  · intro b' hb'
    rw [Finset.mem_filter, Finset.mem_range] at hb'
    obtain ⟨hb1, hb2⟩ := hb'
    exact ⟨(b' : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ZMod.isUnit_iff_coprime b' q).mpr hb2⟩, ZMod.val_cast_of_lt hb1⟩
  · intro b _
    rw [hatSum_eq_trigSum]

/-- The per-modulus bound: `(q/φ(q)) ∑*_{χ mod q} |T(χ)|² ≤ ∑_{(b,q)=1} |S(b/q)|²`. -/
lemma character_bound_per_q (hq : 1 ≤ q) :
    (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      ∑ b ∈ (Finset.range q).filter (·.Coprime q), ‖trigSum a s (b / q)‖ ^ 2 := by
  classical
  have htot : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hT : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (q : ℝ) * ‖∑ n ∈ s, a n * χ n‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 := by
    intro χ hχ
    have hprim : (χ⁻¹).IsPrimitive := by
      rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
        ← DirichletCharacter.isPrimitive_def]
    have h1 := gaussSum_mul_charSum (a := a) (s := s) hχ
    have h3 : ‖gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ s, a n * χ n)‖ ^ 2 =
        (q : ℝ) * ‖∑ n ∈ s, a n * χ n‖ ^ 2 := by
      rw [norm_mul, mul_pow, gaussSum_normSq hprim]
    rw [h1] at h3
    rw [← h3]
  have h4 : (q : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) =
      ∑ χ : DirichletCharacter ℂ q, (if χ.IsPrimitive then
        ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hχ : χ.IsPrimitive
    · rw [if_pos hχ, if_pos hχ, hT χ hχ]
    · rw [if_neg hχ, if_neg hχ, mul_zero]
  have h5 : ∑ χ : DirichletCharacter ℂ q, (if χ.IsPrimitive then
      ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 else 0) ≤
      ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro χ _
    by_cases hχ : χ.IsPrimitive
    · rw [if_pos hχ]
    · rw [if_neg hχ]
      positivity
  have h6 : (q : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      (q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [h4]
    exact h5.trans (le_of_eq (sum_all_char_hatSum (a := a) (s := s)))
  have h7 : (q : ℝ) / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      ∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ htot]
    simpa [mul_comm] using h6
  exact h7.trans (le_of_eq (sum_units_hatSum_eq (a := a) (s := s)))

/-- **The character form of the large sieve** (inequality (2) of Chen's paper):
`∑_{q≤X} (q/φ(q)) ∑*_{χ mod q} |∑_{M<n≤M+N} aₙ χ(n)|² ≤ (X² + πN) ∑|aₙ|²`. -/
theorem large_sieve_character (X M N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0)
      ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0)
      ≤ ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
          ‖trigSum a (Finset.Ioc M (M + N)) (b / q)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' := Finset.mem_Icc.mp hq
        haveI : NeZero q := ⟨by omega⟩
        exact character_bound_per_q (a := a) (s := Finset.Ioc M (M + N)) hq'.1
    _ ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
        additive_large_sieve X M N a

/-- **The dyadic large sieve** (inequality (3) of Chen's paper):
`∑_{D<q≤Q} φ(q)⁻¹ ∑*_{χ mod q} |∑ aₙ χ(n)|² ≪ (Q + N/D) ∑|aₙ|²`,
proved by decomposing `(D, Q]` into dyadic blocks `(2ⁱD, 2ⁱ⁺¹D]` and applying
the character form at each block's top. -/
theorem large_sieve_character_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  refine ⟨8 + 2 * Real.pi, by positivity, fun D Q M N a hD hDQ => ?_⟩
  set s := Finset.Ioc M (M + N)
  set Z := ∑ n ∈ s, ‖a n‖ ^ 2
  set F : ℕ → ℝ := fun q => (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
    if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0)
  have hF : ∀ q, 0 ≤ F q := by
    intro q
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity)
  rcases eq_or_lt_of_le hDQ with rfl | hlt
  · simp only [Finset.Ioc_self, Finset.sum_empty]
    positivity
  · -- D < Q: decompose into dyadic blocks.
    set h := Nat.log 2 ((Q - 1) / D) with hh_def
    have hblock : ∀ i : ℕ, ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q ≤
        (2 ^ (i + 2) * D + Real.pi * N / (2 ^ i * D)) * Z := by
      intro i
      have hDi : (0 : ℝ) < (2 ^ i * D : ℝ) := by positivity
      have hXnn : ∀ q : ℕ, 0 ≤ (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
        intro q
        positivity
      calc ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q
          ≤ (2 ^ i * D : ℝ)⁻¹ * ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D),
              (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_Ioc] at hq
            have hq0 : (0 : ℝ) < q := by
              exact_mod_cast (by omega : 0 < q)
            have htotq : (0:ℝ) < q.totient := by
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
            have hX : 0 ≤ (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) :=
              Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity
            have hrewrite : (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) =
                (q : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ) *
                  (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0)) := by
              field_simp
            change (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
              (2 ^ i * D : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ) *
                (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0))
            rw [hrewrite]
            have hinv : (q : ℝ)⁻¹ ≤ (2 ^ i * D : ℝ)⁻¹ := by
              apply (inv_le_inv₀ hq0 hDi).2
              exact_mod_cast (le_of_lt hq.1)
            simpa [mul_assoc] using
              mul_le_mul_of_nonneg_right hinv (mul_nonneg (by positivity) hX)
        _ ≤ (2 ^ i * D : ℝ)⁻¹ * (((2 ^ (i + 1) * D : ℝ)) ^ 2 + Real.pi * N) * Z := by
            have hext : ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D),
                (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
                ∑ q ∈ Finset.Icc 1 (2 ^ (i + 1) * D), (q : ℝ) / (q.totient : ℝ) *
                  (∑ χ : DirichletCharacter ℂ q,
                    if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro q hq
                rw [Finset.mem_Ioc] at hq
                rw [Finset.mem_Icc]
                exact ⟨by omega, hq.2⟩
              · intro q _ _
                exact hXnn q
            have hls := hext.trans (large_sieve_character (2 ^ (i + 1) * D) M N a)
            simpa only [Z, s, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
              mul_le_mul_of_nonneg_left hls (inv_nonneg.mpr hDi.le)
        _ = (2 ^ (i + 2) * D + Real.pi * N / (2 ^ i * D)) * Z := by
            field_simp
            ring
    have hdisj : Set.PairwiseDisjoint (Finset.range (h + 1))
        (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)) := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro q hq1 hq2
      rw [Finset.mem_Ioc] at hq1 hq2
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        have hsep := Nat.mul_le_mul_right D hpow
        omega
      · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        have hsep := Nat.mul_le_mul_right D hpow
        omega
    have hcover : Finset.Ioc D Q ⊆ (Finset.range (h + 1)).biUnion
        (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)) := by
      intro q hq
      rw [Finset.mem_Ioc] at hq
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 ((q - 1) / D), ?_, ?_⟩
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Nat.log_mono_right (Nat.div_le_div_right (by omega : q - 1 ≤ Q - 1))
      · rw [Finset.mem_Ioc]
        constructor
        · have h1 : 2 ^ Nat.log 2 ((q - 1) / D) * D ≤ q - 1 := by
            have hx : 0 < (q - 1) / D := Nat.div_pos (by omega) (by omega)
            have h2 := Nat.pow_log_le_self 2 (x := (q - 1) / D) hx.ne'
            calc 2 ^ Nat.log 2 ((q - 1) / D) * D
                ≤ ((q - 1) / D) * D := Nat.mul_le_mul_right D h2
              _ ≤ q - 1 := Nat.div_mul_le_self _ _
          omega
        · have h2 : (q - 1) / D < 2 ^ (Nat.log 2 ((q - 1) / D) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
          have h3 : q - 1 < 2 ^ (Nat.log 2 ((q - 1) / D) + 1) * D := by
            exact (Nat.div_lt_iff_lt_mul (by omega : 0 < D)).mp h2
          omega
    have hZ : 0 ≤ Z := Finset.sum_nonneg fun n _ => sq_nonneg ‖a n‖
    have hhpow : 2 ^ h * D ≤ Q := by
      rw [hh_def]
      have hx : 0 < (Q - 1) / D := Nat.div_pos (by omega) (by omega)
      calc
        2 ^ Nat.log 2 ((Q - 1) / D) * D
            ≤ ((Q - 1) / D) * D :=
              Nat.mul_le_mul_right D (Nat.pow_log_le_self 2 hx.ne')
        _ ≤ Q - 1 := Nat.div_mul_le_self _ _
        _ ≤ Q := by omega
    have hpowSum : ∀ k : ℕ, (∑ i ∈ Finset.range k, (2 : ℝ) ^ i) ≤ 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, pow_succ]
          nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
    have hfirst :
        (∑ i ∈ Finset.range (h + 1), (2 ^ (i + 2) * D : ℝ)) ≤ 8 * Q := by
      calc
        (∑ i ∈ Finset.range (h + 1), (2 ^ (i + 2) * D : ℝ)) =
            4 * (D : ℝ) * ∑ i ∈ Finset.range (h + 1), (2 : ℝ) ^ i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ 4 * (D : ℝ) * (2 : ℝ) ^ (h + 1) := by
              gcongr
              exact hpowSum (h + 1)
        _ = 8 * ((2 ^ h * D : ℕ) : ℝ) := by
              push_cast
              rw [pow_succ]
              ring
        _ ≤ 8 * Q := by
              exact_mod_cast (Nat.mul_le_mul_left 8 hhpow)
    have hsecond :
        (∑ i ∈ Finset.range (h + 1), Real.pi * N / (2 ^ i * D)) ≤
          2 * Real.pi * N / D := by
      have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      calc
        (∑ i ∈ Finset.range (h + 1), Real.pi * N / (2 ^ i * D)) =
            (Real.pi * N / D) *
              ∑ i ∈ Finset.range (h + 1), (1 / (2 : ℝ)) ^ i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                rw [div_pow]
                norm_num
                field_simp
        _ ≤ (Real.pi * N / D) * 2 := by
              apply mul_le_mul_of_nonneg_left (sum_geometric_two_le (h + 1))
              positivity
        _ = 2 * Real.pi * N / D := by ring
    have hcoef :
        (∑ i ∈ Finset.range (h + 1),
            ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D))) ≤
          8 * Q + 2 * Real.pi * N / D := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hfirst hsecond
    have hsum :
        ∑ q ∈ Finset.Ioc D Q, F q ≤
          (8 * Q + 2 * Real.pi * N / D) * Z := by
      calc
        ∑ q ∈ Finset.Ioc D Q, F q ≤
            ∑ q ∈ (Finset.range (h + 1)).biUnion
              (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)), F q := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hcover
                intro q _ _
                exact hF q
        _ = ∑ i ∈ Finset.range (h + 1),
              ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q := by
                exact Finset.sum_biUnion hdisj
        _ ≤ ∑ i ∈ Finset.range (h + 1),
              ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D)) * Z := by
                apply Finset.sum_le_sum
                intro i _
                exact hblock i
        _ = (∑ i ∈ Finset.range (h + 1),
              ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D))) * Z := by
                rw [Finset.sum_mul]
        _ ≤ (8 * Q + 2 * Real.pi * N / D) * Z :=
              mul_le_mul_of_nonneg_right hcoef hZ
    have hQ0 : (0 : ℝ) ≤ Q := by positivity
    have hND0 : (0 : ℝ) ≤ (N : ℝ) / D := by positivity
    have hconstant :
        8 * (Q : ℝ) + 2 * Real.pi * N / D ≤
          (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) := by
      calc
        8 * (Q : ℝ) + 2 * Real.pi * N / D ≤
            8 * Q + 2 * Real.pi * N / D +
              (2 * Real.pi * Q + 8 * ((N : ℝ) / D)) := by
                exact le_add_of_nonneg_right
                  (add_nonneg
                    (mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) hQ0)
                    (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) hND0))
        _ = (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) := by ring
    change ∑ q ∈ Finset.Ioc D Q, F q ≤
      (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) * Z
    exact hsum.trans (mul_le_mul_of_nonneg_right hconstant hZ)

end Chen.LargeSieve
