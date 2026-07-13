/-
  Integrality of OEIS A276175:

      a 0 = a 1 = a 2 = a 3 = 1,
      a (n+4) * a n = (a (n+3) + 1) (a (n+2) + 1) (a (n+1) + 1)   ⟹   a n ∈ ℤ.

  Two ingredients:
    * `A276175` — an elementary odd-prime valuation induction proves
      `0 ≤ padicValRat p (a n)` for every odd prime `p`, followed by the
      valuation criterion for rational integers.
    * `Return` — the bound at `p = 2`, via a 44-step return lemma for rational
      points of the tube `1 + 16ℤ₂`.  A finite computation with polynomial jets
      is decided by `native_decide` (`checkerB`) and connected to the rational
      recurrence by the invariant `Rep`.

  `a = seq (win 0)` connects the return argument to the original sequence,
  giving `A276175_integrality`.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Std.Data.HashMap

namespace A276175

/-! ## The sequence -/

/-- OEIS A276175. -/
def a : ℕ → ℚ
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1
  | n + 4 => (a (n + 3) + 1) * (a (n + 2) + 1) * (a (n + 1) + 1) / a n

/-! ## Positivity and the recurrence in product form -/

lemma a_pos : ∀ n, 0 < a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [a]
    | 1 => norm_num [a]
    | 2 => norm_num [a]
    | 3 => norm_num [a]
    | n + 4 =>
      have h0 := ih n (by omega)
      have h1 := ih (n+1) (by omega)
      have h2 := ih (n+2) (by omega)
      have h3 := ih (n+3) (by omega)
      rw [a]; positivity

lemma a_ne (n : ℕ) : a n ≠ 0 := (a_pos n).ne'

/-- The `a`-recurrence in product form. -/
lemma rec_eq (n : ℕ) :
    a (n + 4) * a n = (a (n + 3) + 1) * (a (n + 2) + 1) * (a (n + 1) + 1) := by
  show ((a (n + 3) + 1) * (a (n + 2) + 1) * (a (n + 1) + 1) / a n) * a n = _
  rw [div_mul_cancel₀ _ (a_ne n)]

/-! ## Integrality at every odd prime

`0 ≤ padicValRat q (a n)` for odd `q`, by an elementary "burst confinement"
induction resting on the identity `star` below. -/

/-- `b n = a n + 1`. -/
def b (n : ℕ) : ℚ := a n + 1

lemma b_pos (n : ℕ) : 0 < b n := by have := a_pos n; unfold b; linarith
lemma b_ne (n : ℕ) : b n ≠ 0 := (b_pos n).ne'

/-- The key identity: `b (n+4) * a n = a n + b (n+3) * b (n+2) * b (n+1)`. -/
lemma star (n : ℕ) : b (n + 4) * a n = a n + b (n + 3) * b (n + 2) * b (n + 1) := by
  have h := rec_eq n
  calc b (n + 4) * a n = a (n + 4) * a n + a n := by unfold b; ring
  _ = a n + b (n + 3) * b (n + 2) * b (n + 1) := by rw [h]; unfold b; ring

lemma a4 : a 4 = 8 := by norm_num [a]
lemma a5 : a 5 = 36 := by norm_num [a]
lemma a6 : a 6 = 666 := by norm_num [a]
lemma a7 : a 7 = 222111 := by norm_num [a]
lemma b4 : b 4 = 9 := by norm_num [b, a4]
lemma b5 : b 5 = 37 := by norm_num [b, a5]
lemma b6 : b 6 = 667 := by norm_num [b, a6]
lemma b7 : b 7 = 222112 := by norm_num [b, a7]

section Val

variable (p : ℕ)

lemma val_nat_nonneg (m : ℕ) : 0 ≤ padicValRat p (m : ℚ) := by
  rw [padicValRat.of_nat]; positivity

lemma val_nat_eq_zero {m : ℕ} (h : ¬ p ∣ m) : padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]; rfl

lemma dvd_of_val_pos {m : ℕ} (h : 0 < padicValRat p (m : ℚ)) : p ∣ m := by
  by_contra hd
  rw [val_nat_eq_zero p hd] at h
  exact lt_irrefl 0 h

end Val

/-- `t p n`: the p-adic valuation carried by the "atom" at index `n`. -/
def t (p : ℕ) : ℕ → ℤ
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0
  | n + 4 => padicValRat p (b (n + 4)) - t p n

lemma t_succ (p n : ℕ) : t p (n + 4) = padicValRat p (b (n + 4)) - t p n := rfl
lemma val_b_eq (p n : ℕ) : padicValRat p (b (n + 4)) = t p (n + 4) + t p n := by
  rw [t_succ]; ring
lemma t0 (p : ℕ) : t p 0 = 0 := rfl
lemma t1 (p : ℕ) : t p 1 = 0 := rfl
lemma t2 (p : ℕ) : t p 2 = 0 := rfl
lemma t3 (p : ℕ) : t p 3 = 0 := rfl

section OddPrime

variable (p : ℕ) [hp : Fact p.Prime]

lemma not_dvd_two_pow (hp2 : p ≠ 2) (k : ℕ) : ¬ p ∣ 2 ^ k := fun hd =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
    (hp.out.dvd_of_dvd_pow hd))

lemma val_two_pow_zero (hp2 : p ≠ 2) (k : ℕ) : padicValRat p ((2 ^ k : ℕ) : ℚ) = 0 :=
  val_nat_eq_zero p (not_dvd_two_pow p hp2 k)

/-- Lemma (II). -/
lemma val_a (hp2 : p ≠ 2) (n : ℕ) :
    padicValRat p (a (n + 4)) = t p (n + 3) + t p (n + 2) + t p (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have h8 : (a 4 : ℚ) = ((2 ^ 3 : ℕ) : ℚ) := by rw [a4]; norm_num
      rw [h8, val_two_pow_zero p hp2, t3, t2, t1]; ring
    | 1 =>
      have h : (a 5 : ℚ) = ((2 ^ 2 : ℕ) : ℚ) * ((9 : ℕ) : ℚ) := by rw [a5]; norm_num
      rw [h, padicValRat.mul (by norm_num) (by norm_num), val_two_pow_zero p hp2]
      have ht4 : t p 4 = padicValRat p ((9 : ℕ) : ℚ) := by rw [t_succ, b4, t0]; norm_num
      rw [ht4, t3, t2]; ring
    | 2 =>
      have h : (a 6 : ℚ) = ((2 ^ 1 : ℕ) : ℚ) * ((9 : ℕ) : ℚ) * ((37 : ℕ) : ℚ) := by
        rw [a6]; norm_num
      rw [h, padicValRat.mul (by positivity) (by norm_num),
        padicValRat.mul (by norm_num) (by norm_num), val_two_pow_zero p hp2]
      have ht4 : t p 4 = padicValRat p ((9 : ℕ) : ℚ) := by rw [t_succ, b4, t0]; norm_num
      have ht5 : t p 5 = padicValRat p ((37 : ℕ) : ℚ) := by rw [t_succ, b5, t1]; norm_num
      rw [ht4, ht5, t3]; ring
    | 3 =>
      have h : (a 7 : ℚ) = ((9 : ℕ) : ℚ) * ((37 : ℕ) : ℚ) * ((667 : ℕ) : ℚ) := by
        rw [a7]; norm_num
      rw [h, padicValRat.mul (by positivity) (by norm_num),
        padicValRat.mul (by norm_num) (by norm_num)]
      have ht4 : t p 4 = padicValRat p ((9 : ℕ) : ℚ) := by rw [t_succ, b4, t0]; norm_num
      have ht5 : t p 5 = padicValRat p ((37 : ℕ) : ℚ) := by rw [t_succ, b5, t1]; norm_num
      have ht6 : t p 6 = padicValRat p ((667 : ℕ) : ℚ) := by rw [t_succ, b6, t2]; norm_num
      rw [ht4, ht5, ht6]; ring
    | m + 4 =>
      have hrec := rec_eq (m + 4)
      have h1 : padicValRat p (a (m + 4 + 4)) + padicValRat p (a (m + 4)) =
          padicValRat p (b (m + 4 + 3)) + padicValRat p (b (m + 4 + 2)) +
          padicValRat p (b (m + 4 + 1)) := by
        rw [← padicValRat.mul (a_ne _) (a_ne _)]
        rw [show a (m+4+3) + 1 = b (m+4+3) from rfl, show a (m+4+2) + 1 = b (m+4+2) from rfl,
          show a (m+4+1) + 1 = b (m+4+1) from rfl] at hrec
        rw [hrec, padicValRat.mul (mul_ne_zero (b_ne _) (b_ne _)) (b_ne _),
          padicValRat.mul (b_ne _) (b_ne _)]
      have hprev := ih m (by omega)
      have hb7 := val_b_eq p (m + 3)
      have hb6 := val_b_eq p (m + 2)
      have hb5 := val_b_eq p (m + 1)
      ring_nf at h1 hprev hb7 hb6 hb5 ⊢
      omega

omit hp in
lemma t4_eq : t p 4 = padicValRat p ((9 : ℕ) : ℚ) := by rw [t_succ, b4, t0]; norm_num
omit hp in
lemma t5_eq : t p 5 = padicValRat p ((37 : ℕ) : ℚ) := by rw [t_succ, b5, t1]; norm_num
omit hp in
lemma t6_eq : t p 6 = padicValRat p ((667 : ℕ) : ℚ) := by rw [t_succ, b6, t2]; norm_num
omit hp in
lemma t7_eq : t p 7 = padicValRat p ((222112 : ℕ) : ℚ) := by rw [t_succ, b7, t3]; norm_num

/-- Step for Lemma (III). -/
lemma burst_step (hp2 : p ≠ 2) (k : ℕ)
    (h_nonneg : ∀ j, j ≤ k + 7 → 0 ≤ t p j)
    (h : 0 < t p (k + 8)) :
    t p (k + 7) = 0 ∧ t p (k + 6) = 0 ∧ t p (k + 5) = 0 := by
  have hb := val_b_eq p (k + 4)
  rw [show k + 4 + 4 = k + 8 by omega] at hb
  have hbpos : 0 < padicValRat p (b (k + 8)) := by
    have := h_nonneg (k + 4) (by omega); omega
  have ha := val_a p hp2 (k + 4)
  rw [show k + 4 + 4 = k + 8 by omega, show k + 4 + 3 = k + 7 by omega,
    show k + 4 + 2 = k + 6 by omega, show k + 4 + 1 = k + 5 by omega] at ha
  have h1 : b (k + 8) + -a (k + 8) = 1 := by unfold b; ring
  have hmin := padicValRat.min_le_padicValRat_add (p := p)
    (q := b (k + 8)) (r := -a (k + 8)) (by rw [h1]; norm_num)
  rw [h1, padicValRat.one, padicValRat.neg] at hmin
  have hva : padicValRat p (a (k + 8)) ≤ 0 := by
    rcases min_le_iff.mp hmin with h' | h' <;> omega
  have h7 := h_nonneg (k + 7) (by omega)
  have h6 := h_nonneg (k + 6) (by omega)
  have h5 := h_nonneg (k + 5) (by omega)
  omega

/-- Step for Lemma (I). -/
lemma t_step_nonneg (hp2 : p ≠ 2) (k : ℕ)
    (h_nonneg : ∀ j, j ≤ k + 7 → 0 ≤ t p j)
    (h_burst : 0 < t p (k + 4) →
      t p (k + 3) = 0 ∧ t p (k + 2) = 0 ∧ t p (k + 1) = 0) :
    0 ≤ t p (k + 8) := by
  have htk4 : 0 ≤ t p (k + 4) := h_nonneg (k + 4) (by omega)
  have hb := val_b_eq p (k + 4)
  rw [show k + 4 + 4 = k + 8 by omega] at hb
  have ha8 := val_a p hp2 (k + 4)
  rw [show k + 4 + 4 = k + 8 by omega, show k + 4 + 3 = k + 7 by omega,
    show k + 4 + 2 = k + 6 by omega, show k + 4 + 1 = k + 5 by omega] at ha8
  have hva8 : 0 ≤ padicValRat p (a (k + 8)) := by
    have h7 := h_nonneg (k + 7) (by omega)
    have h6 := h_nonneg (k + 6) (by omega)
    have h5 := h_nonneg (k + 5) (by omega)
    omega
  rcases eq_or_lt_of_le htk4 with hT0 | hTpos
  · have h1 : (1 : ℚ) + a (k + 8) = b (k + 8) := by unfold b; ring
    have hmin := padicValRat.min_le_padicValRat_add (p := p)
      (q := (1 : ℚ)) (r := a (k + 8)) (by rw [h1]; exact b_ne _)
    rw [h1, padicValRat.one] at hmin
    have hvb : 0 ≤ padicValRat p (b (k + 8)) :=
      le_trans (by simp [hva8]) hmin
    omega
  · set T := t p (k + 4) with hT
    obtain ⟨hz3, hz2, hz1⟩ := h_burst hTpos
    have ha4 := val_a p hp2 k
    have hva4 : padicValRat p (a (k + 4)) = 0 := by omega
    have ha5 := val_a p hp2 (k + 1)
    rw [show k + 1 + 4 = k + 5 by omega, show k + 1 + 3 = k + 4 by omega,
      show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at ha5
    have hva5 : padicValRat p (a (k + 5)) = T := by omega
    have ha6 := val_a p hp2 (k + 2)
    rw [show k + 2 + 4 = k + 6 by omega, show k + 2 + 3 = k + 5 by omega,
      show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at ha6
    have hva6 : T ≤ padicValRat p (a (k + 6)) := by
      have := h_nonneg (k + 5) (by omega); omega
    have ha7 := val_a p hp2 (k + 3)
    rw [show k + 3 + 4 = k + 7 by omega, show k + 3 + 3 = k + 6 by omega,
      show k + 3 + 2 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega] at ha7
    have hva7 : T ≤ padicValRat p (a (k + 7)) := by
      have := h_nonneg (k + 6) (by omega)
      have := h_nonneg (k + 5) (by omega)
      omega
    have hvb5 : 0 ≤ padicValRat p (b (k + 5)) := by
      have h := val_b_eq p (k + 1)
      rw [show k + 1 + 4 = k + 5 by omega] at h
      have := h_nonneg (k + 5) (by omega)
      have := h_nonneg (k + 1) (by omega)
      omega
    have hvb6 : 0 ≤ padicValRat p (b (k + 6)) := by
      have h := val_b_eq p (k + 2)
      rw [show k + 2 + 4 = k + 6 by omega] at h
      have := h_nonneg (k + 6) (by omega)
      have := h_nonneg (k + 2) (by omega)
      omega
    have hvb4 : T ≤ padicValRat p (b (k + 4)) := by
      have h := val_b_eq p k
      have := h_nonneg k (by omega)
      omega
    have hap7 := a_pos (k + 7)
    have hap6 := a_pos (k + 6)
    have hap5 := a_pos (k + 5)
    have hbp6 := b_pos (k + 6)
    have hbp5 := b_pos (k + 5)
    have hbp4 := b_pos (k + 4)
    have hvs1 : T ≤ padicValRat p (a (k + 7) * (b (k + 6) * b (k + 5))) := by
      rw [padicValRat.mul (a_ne _) (mul_ne_zero (b_ne _) (b_ne _)),
        padicValRat.mul (b_ne _) (b_ne _)]
      omega
    have hvs2 : T ≤ padicValRat p (a (k + 6) * b (k + 5)) := by
      rw [padicValRat.mul (a_ne _) (b_ne _)]; omega
    have hvs3 : T ≤ padicValRat p (a (k + 5)) := by omega
    have hv12 : T ≤ padicValRat p
        (a (k + 7) * (b (k + 6) * b (k + 5)) + a (k + 6) * b (k + 5)) :=
      le_trans (le_min hvs1 hvs2)
        (padicValRat.min_le_padicValRat_add (p := p) (by positivity))
    have hvX : T ≤ padicValRat p
        (a (k + 7) * (b (k + 6) * b (k + 5)) + a (k + 6) * b (k + 5) + a (k + 5)) :=
      le_trans (le_min hv12 hvs3)
        (padicValRat.min_le_padicValRat_add (p := p) (by positivity))
    have hkey : b (k + 8) * a (k + 4) = b (k + 4) +
        (a (k + 7) * (b (k + 6) * b (k + 5)) + a (k + 6) * b (k + 5) + a (k + 5)) := by
      have hstar := star (k + 4)
      rw [show k + 4 + 4 = k + 8 by omega, show k + 4 + 3 = k + 7 by omega,
        show k + 4 + 2 = k + 6 by omega, show k + 4 + 1 = k + 5 by omega] at hstar
      unfold b
      unfold b at hstar
      linarith [hstar]
    have hvkey : T ≤ padicValRat p (b (k + 8) * a (k + 4)) := by
      rw [hkey]
      exact le_trans (le_min hvb4 hvX)
        (padicValRat.min_le_padicValRat_add (p := p) (by positivity))
    have hmul : padicValRat p (b (k + 8) * a (k + 4)) =
        padicValRat p (b (k + 8)) + padicValRat p (a (k + 4)) :=
      padicValRat.mul (b_ne _) (a_ne _)
    have hvb8 : T ≤ padicValRat p (b (k + 8)) := by omega
    omega

/-- Lemmas (I) and (III), combined, by strong induction. -/
lemma main_induction (hp2 : p ≠ 2) : ∀ n, (0 ≤ t p n) ∧
    (∀ k, n = k + 4 → 0 < t p n →
      t p (k + 3) = 0 ∧ t p (k + 2) = 0 ∧ t p (k + 1) = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨by rw [t0], fun k hk => absurd hk (by omega)⟩
    | 1 => exact ⟨by rw [t1], fun k hk => absurd hk (by omega)⟩
    | 2 => exact ⟨by rw [t2], fun k hk => absurd hk (by omega)⟩
    | 3 => exact ⟨by rw [t3], fun k hk => absurd hk (by omega)⟩
    | 4 =>
      refine ⟨by rw [t4_eq]; exact val_nat_nonneg p 9, fun k hk _ => ?_⟩
      obtain rfl : k = 0 := by omega
      exact ⟨t3 p, t2 p, t1 p⟩
    | 5 =>
      refine ⟨by rw [t5_eq]; exact val_nat_nonneg p 37, fun k hk h5 => ?_⟩
      obtain rfl : k = 1 := by omega
      rw [t5_eq] at h5
      have hd : p ∣ 37 := dvd_of_val_pos p h5
      have hp37 : p = 37 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hd
      subst hp37
      refine ⟨?_, t3 _, t2 _⟩
      rw [t4_eq]
      exact val_nat_eq_zero 37 (by decide)
    | 6 =>
      refine ⟨by rw [t6_eq]; exact val_nat_nonneg p 667, fun k hk h6 => ?_⟩
      obtain rfl : k = 2 := by omega
      rw [t6_eq] at h6
      have hd : p ∣ 667 := dvd_of_val_pos p h6
      have hd' : p ∣ 23 * 29 := by rwa [show (23 * 29 : ℕ) = 667 by norm_num]
      rcases (Nat.Prime.dvd_mul hp.out).mp hd' with h | h
      · have hp23 : p = 23 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h
        subst hp23
        exact ⟨by rw [t5_eq]; exact val_nat_eq_zero 23 (by decide),
               by rw [t4_eq]; exact val_nat_eq_zero 23 (by decide), t3 _⟩
      · have hp29 : p = 29 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h
        subst hp29
        exact ⟨by rw [t5_eq]; exact val_nat_eq_zero 29 (by decide),
               by rw [t4_eq]; exact val_nat_eq_zero 29 (by decide), t3 _⟩
    | 7 =>
      refine ⟨by rw [t7_eq]; exact val_nat_nonneg p 222112, fun k hk h7 => ?_⟩
      obtain rfl : k = 3 := by omega
      rw [t7_eq] at h7
      have hd : p ∣ 222112 := dvd_of_val_pos p h7
      have hd' : p ∣ 2 ^ 5 * (11 * 631) := by
        rwa [show (2 ^ 5 * (11 * 631) : ℕ) = 222112 by norm_num]
      rcases (Nat.Prime.dvd_mul hp.out).mp hd' with h | h
      · exact absurd h (not_dvd_two_pow p hp2 5)
      · rcases (Nat.Prime.dvd_mul hp.out).mp h with h' | h'
        · have hp11 : p = 11 :=
            (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h'
          subst hp11
          exact ⟨by rw [t6_eq]; exact val_nat_eq_zero 11 (by decide),
                 by rw [t5_eq]; exact val_nat_eq_zero 11 (by decide),
                 by rw [t4_eq]; exact val_nat_eq_zero 11 (by decide)⟩
        · have hp631 : p = 631 :=
            (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h'
          subst hp631
          exact ⟨by rw [t6_eq]; exact val_nat_eq_zero 631 (by decide),
                 by rw [t5_eq]; exact val_nat_eq_zero 631 (by decide),
                 by rw [t4_eq]; exact val_nat_eq_zero 631 (by decide)⟩
    | k + 8 =>
      have h_nonneg : ∀ j, j ≤ k + 7 → 0 ≤ t p j := fun j hj =>
        (ih j (by omega)).1
      have h_burst : 0 < t p (k + 4) →
          t p (k + 3) = 0 ∧ t p (k + 2) = 0 ∧ t p (k + 1) = 0 :=
        (ih (k + 4) (by omega)).2 k rfl
      refine ⟨t_step_nonneg p hp2 k h_nonneg h_burst, fun k' hk' h => ?_⟩
      obtain rfl : k' = k + 4 := by omega
      have hres := burst_step p hp2 k h_nonneg h
      rw [show k + 4 + 3 = k + 7 by omega, show k + 4 + 2 = k + 6 by omega,
        show k + 4 + 1 = k + 5 by omega]
      exact hres

/-- for every odd prime `p`, `0 ≤ padicValRat p (a n)`. -/
theorem odd_prime_val_nonneg (hp2 : p ≠ 2) (n : ℕ) :
    0 ≤ padicValRat p (a n) := by
  match n with
  | 0 => rw [show a 0 = 1 from rfl, padicValRat.one]
  | 1 => rw [show a 1 = 1 from rfl, padicValRat.one]
  | 2 => rw [show a 2 = 1 from rfl, padicValRat.one]
  | 3 => rw [show a 3 = 1 from rfl, padicValRat.one]
  | m + 4 =>
    rw [val_a p hp2 m]
    have h3 := (main_induction p hp2 (m + 3)).1
    have h2 := (main_induction p hp2 (m + 2)).1
    have h1 := (main_induction p hp2 (m + 1)).1
    omega

end OddPrime

/-! ## The bridge to integrality -/

/-- If `0 ≤ padicValRat p r` for every prime `p`, then `r` is an integer. -/
lemma exists_int_of_all_val_nonneg (r : ℚ)
    (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p r) : ∃ z : ℤ, r = z := by
  refine ⟨r.num, ?_⟩
  have hden : r.den = 1 := by
    by_contra hd
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
    haveI : Fact q.Prime := ⟨hq⟩
    have hnum : padicValInt q r.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hdvd
      have h1 : q ∣ r.num.natAbs := Int.ofNat_dvd_left.mp hdvd
      have h2 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hqd
      rw [r.reduced] at h2
      exact hq.one_lt.ne' (Nat.dvd_one.mp h2)
    have hden1 : 1 ≤ padicValNat q r.den :=
      one_le_padicValNat_of_dvd r.den_pos.ne' hqd
    have hval : padicValRat q r < 0 := by
      have hdef : padicValRat q r = padicValInt q r.num - padicValNat q r.den := rfl
      rw [hdef]; omega
    exact absurd (h q hq) (not_le.mpr hval)
  exact ((Rat.den_eq_one_iff r).mp hden).symm

/-- given 2-adic nonnegativity, every term of `a` is an integer. -/
theorem integrality (h2 : ∀ n, 0 ≤ padicValRat 2 (a n)) (n : ℕ) :
    ∃ z : ℤ, a n = z := by
  apply exists_int_of_all_val_nonneg
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact h2 n
  · exact odd_prime_val_nonneg p hp2 n


end A276175

/-! ## Part 2: the 2-adic bound `∀ n, 0 ≤ padicValRat 2 (a n)`

    Work in `R = ℤ₂[[z₀,z₁,z₂,z₃]]` with `Aᵢ = 1 + 16 zᵢ`.  Writing
    `Aₙ = 2^{wₙ} Uₙ` (`Uₙ` a unit series), the recurrence gives the unit step
    `U_{n+4} = U_n⁻¹ H_{n+1} H_{n+2} H_{n+3}`, `H_j = (1+2^{w_j}U_j)/2^{t_j}`.

    Each `Uₙ` is tracked as a polynomial with coefficients modulo `2^{pₙ}`.  The
    finite 44-step run is `native_decide`d (`checkerB`).  The rest of this section
    turns those finite booleans into real 2-adic facts via a `Represents` relation
    `Rep` (polynomial + precision ⇒ actual 2-adic unit for every tube window), the
    step-preservation lemma `step_prep`, the 44-step induction `reps`, the
    return-to-tube lemma, and the block induction `val_nonneg`.

    Bridge to real values: `normS` is a sort∘group∘reduce∘drop normal form that is
    provably `peval`-invariant up to `2^p` (`peval_normS_close`); `Close k x y`
    denotes `v₂(x − y) ≥ k`, with its calculus below. -/

namespace Return
open Std

abbrev Mon := ℕ × ℕ × ℕ × ℕ
abbrev Poly := List (Mon × Int)

def monMul (a b : Mon) : Mon := (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2+b.2.2.2)
def mon0 : Mon := (0,0,0,0)

/-- evaluate a monomial at a point `c` -/
def monEval (m : Mon) (c : Fin 4 → ℚ) : ℚ :=
  c 0 ^ m.1 * c 1 ^ m.2.1 * c 2 ^ m.2.2.1 * c 3 ^ m.2.2.2

/-- evaluate a polynomial at a point `c` -/
def peval (P : Poly) (c : Fin 4 → ℚ) : ℚ := (P.map (fun t => (t.2 : ℚ) * monEval t.1 c)).sum

@[simp] lemma peval_nil (c) : peval [] c = 0 := rfl

lemma peval_cons (t : Mon × Int) (P : Poly) (c) :
    peval (t :: P) c = (t.2 : ℚ) * monEval t.1 c + peval P c := rfl

lemma peval_append (P Q : Poly) (c) : peval (P ++ Q) c = peval P c + peval Q c := by
  simp [peval, List.map_append, List.sum_append]

lemma monEval_mul (a b : Mon) (c) : monEval (monMul a b) c = monEval a c * monEval b c := by
  simp only [monEval, monMul, pow_add]; ring

lemma peval_mapMul (t : Mon × Int) (Q : Poly) (c) :
    peval (Q.map (fun (b, y) => (monMul t.1 b, t.2 * y))) c
      = (t.2 : ℚ) * monEval t.1 c * peval Q c := by
  induction Q with
  | nil => simp [peval]
  | cons u Q ih =>
    simp only [List.map_cons, peval_cons, ih, monEval_mul]
    push_cast
    ring

/-- evaluation of the raw (ungrouped, unreduced) product list is the product -/
lemma peval_flatMul (P Q : Poly) (c) :
    peval (P.flatMap (fun (a, x) => Q.map (fun (b, y) => (monMul a b, x * y)))) c
      = peval P c * peval Q c := by
  induction P with
  | nil => simp [peval]
  | cons t P ih =>
    rw [List.flatMap_cons, peval_append, ih, peval_cons, peval_mapMul]
    ring

/-! ### Reduction and zero-dropping preserve `peval` up to a `2^p` multiple -/

/-- dropping zero-coefficient entries does not change `peval` -/
lemma peval_filter_ne0 (P : Poly) (c) :
    peval (P.filter (fun t => t.2 != 0)) c = peval P c := by
  induction P with
  | nil => simp [peval]
  | cons t P ih =>
    rw [List.filter_cons]
    by_cases h : (t.2 != 0) = true
    · rw [if_pos h, peval_cons, peval_cons, ih]
    · rw [if_neg h, ih]
      simp only [bne_iff_ne, ne_eq, not_not] at h
      simp [peval_cons, h]

/-- reducing every coefficient mod `2^p` changes `peval` by `2^p` times an
    integer-coefficient polynomial's evaluation -/
lemma peval_reduce (p : Nat) (P : Poly) (c) :
    peval (P.map (fun t => (t.1, t.2 % 2 ^ p))) c
      = peval P c - (2 ^ p : ℚ) * peval (P.map (fun t => (t.1, t.2 / 2 ^ p))) c := by
  induction P with
  | nil => simp [peval]
  | cons t P ih =>
    simp only [List.map_cons, peval_cons, ih]
    have key : ((t.2 % 2 ^ p : Int) : ℚ) = (t.2 : ℚ) - (2 ^ p : ℚ) * ((t.2 / 2 ^ p : Int) : ℚ) := by
      have hi : (t.2 % 2 ^ p : Int) = t.2 - 2 ^ p * (t.2 / 2 ^ p) := by
        linarith [Int.mul_ediv_add_emod t.2 (2 ^ p)]
      rw [hi]; push_cast; ring
    rw [key]; ring

/-! ### Grouping like terms preserves `peval` -/

/-- `peval` is invariant under permutations. -/
lemma peval_perm {P Q : Poly} (h : P.Perm Q) (c) : peval P c = peval Q c :=
  (h.map _).sum_eq

/-- one grouping step: combine `t` into the head of `acc` if the monomial matches -/
def gstep (acc : Poly) (t : Mon × Int) : Poly :=
  match acc with
  | (m, a) :: rest => if t.1 == m then (m, a + t.2) :: rest else t :: acc
  | [] => [t]

/-- combine adjacent equal monomials (correct grouping when sorted) -/
def groupAdj (s : Poly) : Poly := (s.foldl gstep []).reverse

lemma peval_gstep (acc : Poly) (t : Mon × Int) (c) :
    peval (gstep acc t) c = peval acc c + (t.2 : ℚ) * monEval t.1 c := by
  cases acc with
  | nil => simp [gstep, peval_cons, peval_nil]
  | cons h rest =>
    simp only [gstep]
    by_cases hk : (t.1 == h.1) = true
    · rw [if_pos hk]
      rw [beq_iff_eq] at hk
      simp only [peval_cons]; rw [hk]; push_cast; ring
    · rw [if_neg hk]
      simp only [peval_cons]; ring

lemma peval_foldl_gstep (s : Poly) (c) :
    ∀ acc, peval (s.foldl gstep acc) c = peval acc c + peval s c := by
  induction s with
  | nil => intro acc; simp [peval_nil]
  | cons t s ih => intro acc; rw [List.foldl_cons, ih, peval_gstep, peval_cons]; ring

lemma peval_reverse (P : Poly) (c) : peval (P.reverse) c = peval P c :=
  peval_perm (List.reverse_perm P) c

lemma peval_groupAdj (s : Poly) (c) : peval (groupAdj s) c = peval s c := by
  unfold groupAdj
  rw [peval_reverse, peval_foldl_gstep]
  simp [peval_nil]

/-! ### The normal form `normS` and its evaluation split -/

def monLe (a b : Mon) : Bool :=
  if a.1 == b.1 then
    if a.2.1 == b.2.1 then
      if a.2.2.1 == b.2.2.1 then Nat.ble a.2.2.2 b.2.2.2 else Nat.ble a.2.2.1 b.2.2.1
    else Nat.ble a.2.1 b.2.1
  else Nat.ble a.1 b.1

def reduceDrop (p : Nat) (P : Poly) : Poly :=
  (P.map (fun t => (t.1, t.2 % 2 ^ p))).filter (fun t => t.2 != 0)

def normS (p : Nat) (raw : Poly) : Poly :=
  reduceDrop p (groupAdj (raw.mergeSort (fun x y => monLe x.1 y.1)))

lemma peval_reduceDrop (p : Nat) (P : Poly) (c) :
    peval (reduceDrop p P) c
      = peval P c - (2 ^ p : ℚ) * peval (P.map (fun t => (t.1, t.2 / 2 ^ p))) c := by
  unfold reduceDrop
  rw [peval_filter_ne0, peval_reduce]

lemma peval_normS (p : Nat) (raw : Poly) (c) :
    peval (normS p raw) c
      = peval raw c - (2 ^ p : ℚ)
        * peval ((groupAdj (raw.mergeSort (fun x y => monLe x.1 y.1))).map
            (fun t => (t.1, t.2 / 2 ^ p))) c := by
  unfold normS
  rw [peval_reduceDrop, peval_groupAdj, peval_perm (List.mergeSort_perm _ _)]

/-! ### 2-adic integers and the norm-closeness lemma -/

lemma v2_two_pow (α : ℕ) : padicValRat 2 ((2 : ℚ) ^ α) = α := by
  rw [padicValRat.pow (by norm_num), show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    padicValRat.self (by norm_num)]
  ring

/-- `x` is a 2-adic integer. -/
def Int2 (x : ℚ) : Prop := x = 0 ∨ 0 ≤ padicValRat 2 x

lemma Int2.zero : Int2 0 := Or.inl rfl

lemma Int2_intCast (n : ℤ) : Int2 (n : ℚ) := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inl (by exact_mod_cast h)
  · right
    rcases Int.natAbs_eq n with he | he
    · rw [he]; simp only [Int.cast_natCast]; rw [padicValRat.of_nat]; positivity
    · rw [he]; simp only [Int.cast_neg, Int.cast_natCast, padicValRat.neg]
      rw [padicValRat.of_nat]; positivity

lemma Int2.mul {x y : ℚ} (hx : Int2 x) (hy : Int2 y) : Int2 (x * y) := by
  by_cases hx0 : x = 0
  · exact Or.inl (by rw [hx0]; ring)
  by_cases hy0 : y = 0
  · exact Or.inl (by rw [hy0]; ring)
  right
  have vx : 0 ≤ padicValRat 2 x := hx.resolve_left hx0
  have vy : 0 ≤ padicValRat 2 y := hy.resolve_left hy0
  rw [padicValRat.mul hx0 hy0]; omega

lemma Int2.pow {x : ℚ} (hx : Int2 x) (n : ℕ) : Int2 (x ^ n) := by
  induction n with
  | zero => exact Or.inr (by rw [pow_zero, padicValRat.one])
  | succ n ih => rw [pow_succ]; exact ih.mul hx

lemma Int2.add {x y : ℚ} (hx : Int2 x) (hy : Int2 y) : Int2 (x + y) := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]; exact hy
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]; exact hx
  by_cases h : x + y = 0
  · exact Or.inl h
  right
  have vx : 0 ≤ padicValRat 2 x := hx.resolve_left hx0
  have vy : 0 ≤ padicValRat 2 y := hy.resolve_left hy0
  have := padicValRat.min_le_padicValRat_add (p := 2) (q := x) (r := y) h
  omega

/-- the tube: all coordinates are 2-adic integers -/
def Tube (c : Fin 4 → ℚ) : Prop := ∀ i, Int2 (c i)

lemma monEval_Int2 {c} (hc : Tube c) (m : Mon) : Int2 (monEval m c) := by
  unfold monEval
  exact ((((hc 0).pow m.1).mul ((hc 1).pow m.2.1)).mul ((hc 2).pow m.2.2.1)).mul
    ((hc 3).pow m.2.2.2)

lemma peval_Int2 {c} (hc : Tube c) (P : Poly) : Int2 (peval P c) := by
  induction P with
  | nil => exact Int2.zero
  | cons t P ih => rw [peval_cons]; exact ((Int2_intCast t.2).mul (monEval_Int2 hc t.1)).add ih

/-- **norm-closeness**: on the tube, `normS p raw` evaluates 2-adically within
    `2^p` of the raw list. -/
lemma peval_normS_close (p : Nat) (raw : Poly) {c} (hc : Tube c) :
    peval (normS p raw) c = peval raw c ∨
      (p : ℤ) ≤ padicValRat 2 (peval (normS p raw) c - peval raw c) := by
  rw [peval_normS]
  set D := (groupAdj (raw.mergeSort (fun x y => monLe x.1 y.1))).map
    (fun t => (t.1, t.2 / 2 ^ p)) with hD
  rcases eq_or_ne (peval D c) 0 with hz | hz
  · left; rw [hz]; ring
  · right
    have hdiff : (peval raw c - (2 ^ p : ℚ) * peval D c) - peval raw c
        = -((2 ^ p : ℚ) * peval D c) := by ring
    rw [hdiff, padicValRat.neg,
      padicValRat.mul (by positivity) hz, v2_two_pow]
    have vD : 0 ≤ padicValRat 2 (peval D c) := (peval_Int2 hc D).resolve_left hz
    omega

/-! ### 2-adic closeness calculus: `Close k x y` means `x = y` or `v₂(x−y) ≥ k` -/

def Close (k : ℤ) (x y : ℚ) : Prop := x = y ∨ k ≤ padicValRat 2 (x - y)

namespace Close

lemma refl (k : ℤ) (x : ℚ) : Close k x x := Or.inl rfl

lemma mono {k k' : ℤ} {x y : ℚ} (h : k' ≤ k) (hc : Close k x y) : Close k' x y :=
  hc.imp id fun h' => _root_.le_trans h h'

lemma cases' {k : ℤ} {x y : ℚ} (h : Close k x y) :
    x = y ∨ (x - y ≠ 0 ∧ k ≤ padicValRat 2 (x - y)) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨sub_ne_zero.mpr hxy, h⟩

lemma trans {k : ℤ} {x y z : ℚ} (h1 : Close k x y) (h2 : Close k y z) :
    Close k x z := by
  rcases h1.cases' with rfl | ⟨h1n, h1v⟩
  · exact h2
  · rcases h2.cases' with rfl | ⟨h2n, h2v⟩
    · exact Or.inr h1v
    · by_cases hs : x = z
      · exact Or.inl hs
      · right
        have key : x - z = (x - y) + (y - z) := by ring
        rw [key]
        have := padicValRat.min_le_padicValRat_add (p := 2)
          (q := x - y) (r := y - z) (by rw [← key]; exact sub_ne_zero.mpr hs)
        omega

lemma add_left (d : ℚ) {k : ℤ} {x y : ℚ} (h : Close k x y) :
    Close k (d + x) (d + y) := by
  rcases h with rfl | h
  · exact refl k _
  · right; rwa [show d + x - (d + y) = x - y by ring]

lemma mul {k : ℤ} {x y X Y : ℚ}
    (hx : x ≠ 0) (_ : 0 ≤ padicValRat 2 x)
    (hY : Y ≠ 0) (_ : 0 ≤ padicValRat 2 Y)
    (h1 : Close k x X) (h2 : Close k y Y) : Close k (x * y) (X * Y) := by
  have step1 : Close k (x * y) (x * Y) := by
    rcases h2.cases' with rfl | ⟨h2n, h2v⟩
    · exact refl k _
    · right
      rw [show x * y - x * Y = x * (y - Y) by ring, padicValRat.mul hx h2n]
      omega
  have step2 : Close k (x * Y) (X * Y) := by
    rcases h1.cases' with rfl | ⟨h1n, h1v⟩
    · exact refl k _
    · right
      rw [show x * Y - X * Y = (x - X) * Y by ring, padicValRat.mul h1n hY]
      omega
  exact step1.trans step2

lemma inv {k : ℤ} {x X : ℚ} (hx : x ≠ 0) (hX : X ≠ 0)
    (hxv : padicValRat 2 x = 0) (hXv : padicValRat 2 X = 0)
    (h : Close k x X) : Close k x⁻¹ X⁻¹ := by
  rcases h.cases' with rfl | ⟨hn, hv⟩
  · exact refl k _
  · right
    have key : x⁻¹ - X⁻¹ = (X - x) / (x * X) := by field_simp
    have hXx : X - x ≠ 0 := fun hc => hn (by linarith [sub_eq_zero.mp hc])
    rw [key, padicValRat.div hXx (mul_ne_zero hx hX),
      padicValRat.mul hx hX, hxv, hXv,
      show X - x = -(x - X) by ring, padicValRat.neg]
    omega

lemma scale {k : ℤ} {x X : ℚ} (α : ℕ) (h : Close k x X) :
    Close (k + α) ((2:ℚ)^α * x) ((2:ℚ)^α * X) := by
  rcases h.cases' with rfl | ⟨hn, hv⟩
  · exact refl _ _
  · right
    rw [show (2:ℚ)^α * x - (2:ℚ)^α * X = (2:ℚ)^α * (x - X) by ring,
      padicValRat.mul (by positivity) hn, v2_two_pow]
    omega

lemma val_eq {k β : ℤ} {x X : ℚ} (hX : X ≠ 0)
    (hv : padicValRat 2 X = β) (hβ : β < k) (h : Close k x X) :
    x ≠ 0 ∧ padicValRat 2 x = β := by
  rcases h.cases' with rfl | ⟨hn, hvk⟩
  · exact ⟨hX, hv⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      have : padicValRat 2 (0 - X) = β := by
        rw [show (0:ℚ) - X = -X by ring, padicValRat.neg, hv]
      omega
    refine ⟨hx0, ?_⟩
    have h1 : padicValRat 2 x ≥ min β k := by
      have := padicValRat.min_le_padicValRat_add (p := 2)
        (q := X) (r := x - X) (by rw [show X + (x - X) = x by ring]; exact hx0)
      rw [hv] at this
      rw [show X + (x - X) = x by ring] at this
      omega
    have h2 : β ≥ min (padicValRat 2 x) k := by
      have := padicValRat.min_le_padicValRat_add (p := 2)
        (q := x) (r := X - x) (by rw [show x + (X - x) = X by ring]; exact hX)
      rw [show x + (X - x) = X by ring, hv] at this
      rw [show X - x = -(x - X) by ring, padicValRat.neg] at this
      omega
    omega

end Close

/-! ### The window sequence and the base representation -/

def W : List Nat := ([0,0,0,0,3,2,1,0,2,3,4] ++ [0,0,0,0,3,2,1,0,2,3,4]
  ++ [0,0,0,0,4,3,2,0,1,2,3] ++ [0,0,0,0,4,3,2,0,1,2,3])
def T : List Nat := ([1,1,1,1,0,0,0,5,0,0,0] ++ [2,1,1,1,0,0,0,5,0,0,0]
  ++ [2,1,1,2,0,0,0,5,0,0,0] ++ [1,1,1,2,0,0,0,5,0,0,0])
def Wn (n : Nat) : Nat := W.getD (n % 44) 0
def Tn (n : Nat) : Nat := T.getD (n % 44) 0

/-- the A276175-type sequence generated by a 4-term window `w` -/
def seq (w : Fin 4 → ℚ) : ℕ → ℚ
  | 0 => w 0 | 1 => w 1 | 2 => w 2 | 3 => w 3
  | n + 4 => (seq w (n + 3) + 1) * (seq w (n + 2) + 1) * (seq w (n + 1) + 1) / seq w n

/-- the perturbation window `A i = 1 + 16 z_i` -/
def win (c : Fin 4 → ℚ) : Fin 4 → ℚ := fun i => 1 + 16 * c i

def unitMon : Fin 4 → Mon
  | 0 => (1,0,0,0) | 1 => (0,1,0,0) | 2 => (0,0,1,0) | 3 => (0,0,0,1)

lemma monEval_unitMon (i : Fin 4) (c) : monEval (unitMon i) c = c i := by
  fin_cases i <;> simp [monEval, unitMon]

/-- initial jet `U_i = 1 + 16 z_i` -/
def Uinit (i : Fin 4) : Poly := [(mon0, 1), (unitMon i, 16)]

lemma peval_Uinit (i : Fin 4) (c) : peval (Uinit i) c = 1 + 16 * c i := by
  simp only [Uinit, peval_cons, peval_nil, monEval_unitMon]
  simp [monEval, mon0]

/-- on the tube, `1 + 16 z_i` is a 2-adic unit of valuation 0 -/
lemma val_win (c : Fin 4 → ℚ) (hc : Tube c) (i : Fin 4) :
    win c i ≠ 0 ∧ padicValRat 2 (win c i) = 0 := by
  have hcl : Close 4 (win c i) 1 := by
    by_cases h0 : c i = 0
    · left; simp [win, h0]
    · right
      have hv : 0 ≤ padicValRat 2 (c i) := (hc i).resolve_left h0
      have heq : win c i - 1 = (2:ℚ)^4 * c i := by simp only [win]; ring
      rw [heq, padicValRat.mul (by positivity) h0, v2_two_pow]
      omega
  exact hcl.val_eq one_ne_zero padicValRat.one (by norm_num)

/-- `Represents`: the unit `seq/2^{w_n}` is 2-adically `p`-close to `peval P`,
    with valuation exactly `w_n`. -/
def Rep (c : Fin 4 → ℚ) (n : ℕ) (P : Poly) (p : Nat) : Prop :=
  seq (win c) n ≠ 0 ∧
  padicValRat 2 (seq (win c) n) = (Wn n : ℤ) ∧
  Close (p : ℤ) (seq (win c) n / 2 ^ (Wn n)) (peval P c)

/-- base case at one index -/
lemma rep_init (c : Fin 4 → ℚ) (hc : Tube c) (p : Nat) (i : Fin 4) (hw : Wn i.val = 0) :
    Rep c i.val (Uinit i) p := by
  have hs : seq (win c) i.val = win c i := by fin_cases i <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; exact (val_win c hc i).1
  · rw [hs, hw]; simpa using (val_win c hc i).2
  · rw [hs, hw, pow_zero, div_one, peval_Uinit]
    exact Or.inl rfl

/-- base case: the four initial jets represent the window, at any precision. -/
lemma rep_base (c : Fin 4 → ℚ) (hc : Tube c) (p : Nat) :
    Rep c 0 (Uinit 0) p ∧ Rep c 1 (Uinit 1) p ∧ Rep c 2 (Uinit 2) p ∧ Rep c 3 (Uinit 3) p :=
  ⟨rep_init c hc p 0 rfl, rep_init c hc p 1 rfl, rep_init c hc p 2 rfl, rep_init c hc p 3 rfl⟩

/-! ### The finite checker (decided by `native_decide`) -/

def padd (p : Nat) (P Q : Poly) : Poly := normS p (P ++ Q)
def pmul (p : Nat) (P Q : Poly) : Poly :=
  normS p (P.flatMap (fun (a, x) => Q.map (fun (b, y) => (monMul a b, x * y))))
def pconst (x : Int) : Poly := if x == 0 then [] else [(mon0, x)]
def pscale (s : Nat) (P : Poly) : Poly := P.map (fun (m, x) => (m, x * 2 ^ s))
def pdiv2 (s : Nat) (P : Poly) : Poly := P.map (fun (m, x) => (m, x / 2 ^ s))
def cc (P : Poly) : Int := ((P.filter (fun t => t.1 == mon0)).map (fun t => t.2)).sum

/-- all NON-constant coefficients are divisible by `2^m`. -/
def ndiv (m : Nat) (P : Poly) : Bool :=
  (P.filter (fun t => t.1 != mon0)).all (fun t => t.2 % 2 ^ m == 0)
/-- `x` has 2-adic valuation exactly `m`. -/
def dvdExact (m : Nat) (x : Int) : Bool := (x % 2 ^ m == 0) && (x % 2 ^ (m+1) != 0)
def allDiv (p s : Nat) (P : Poly) : Bool := P.all (fun (_, x) => x % 2 ^ p % 2 ^ s == 0)

def pinv (p : Nat) (P : Poly) : Poly :=
  let rec go (kp : Nat) (inv : Poly) (fuel : Nat) : Poly := match fuel with
    | 0 => inv
    | fuel+1 => if kp ≥ p then inv else
        let np := min (2*kp) p
        let uv := pmul np P inv
        let two_minus := padd np (pconst 2) (uv.map (fun (k, x) => (k, -x)))
        go np (pmul np inv two_minus) fuel
  go 1 (pconst 1) (p + 2)

structure JetP where
  poly : Poly
  prec : Nat

def stepC (U : Nat → JetP) (n : Nat) : JetP × Bool :=
  let mk (j : Nat) : Poly × Nat × Bool :=
    let Uj := U (n + j)
    let w := Wn (n+j)
    let t := Tn (n+j)
    let expr := padd (Uj.prec + w) (pscale w Uj.poly) (pconst 1)
    let factor := pdiv2 t expr
    (factor, Uj.prec + w - t,
     allDiv (Uj.prec + w) t expr && (cc factor % 2 == 1) && ndiv 1 factor)
  let f1 := mk 1
  let f2 := mk 2
  let f3 := mk 3
  let pmin := min f1.2.1 (min f2.2.1 f3.2.1)
  let Un := U n
  let numer := pmul pmin (pmul pmin f1.1 f2.1) f3.1
  let pd := min pmin Un.prec
  let inv := pinv pd Un.poly
  (⟨pmul pd numer inv, pd⟩,
    f1.2.2 && f2.2.2 && f3.2.2 && (pmul pd Un.poly inv == pconst 1))

/-- `buildJetsL k` = the jets and the AND of step-validity flags for the first
    `k` steps. -/
def buildJetsL (k : Nat) : List JetP × Bool :=
  (List.range k).foldl
    (fun Uok n =>
      let (jp, b) := stepC (fun i => Uok.1.getD i ⟨[], 1⟩) n
      (Uok.1 ++ [jp], Uok.2 && b))
    ([⟨Uinit 0, 34⟩, ⟨Uinit 1, 34⟩, ⟨Uinit 2, 34⟩, ⟨Uinit 3, 34⟩], true)

def jet (n : Nat) : JetP := (buildJetsL 44).1.getD n ⟨[], 1⟩

def checkerB : Bool :=
  let B := buildJetsL 44
  let g := fun n => B.1.getD n ⟨[], 1⟩
  B.2 &&
  ((List.range 48).all (fun n =>
    decide (1 ≤ (g n).prec) &&
    (if Wn n == 0 then
      decide ((g n).prec > Tn n) && dvdExact (Tn n) (1 + cc (g n).poly)
        && ndiv (Tn n + 1) (g n).poly
     else Tn n == 0))) &&
  ((List.range' 44 4).all (fun n =>
    decide ((g n).prec ≥ 4) && (cc (g n).poly % 16 == 1) && ndiv 4 (g n).poly))

theorem checkerB_ok : checkerB = true := by native_decide

lemma Wn_congr {a b : Nat} (h : a % 44 = b % 44) : Wn a = Wn b := by unfold Wn; rw [h]
lemma Tn_congr {a b : Nat} (h : a % 44 = b % 44) : Tn a = Tn b := by unfold Tn; rw [h]

/-- valuation balance of the word/atom arrays. -/
lemma balance (n : Nat) :
    (Wn (n+4) : ℤ) + Wn n = Tn (n+1) + Tn (n+2) + Tn (n+3) := by
  rw [Wn_congr (a := n+4) (b := n%44+4) (by omega), Wn_congr (a := n) (b := n%44) (by omega),
      Tn_congr (a := n+1) (b := n%44+1) (by omega), Tn_congr (a := n+2) (b := n%44+2) (by omega),
      Tn_congr (a := n+3) (b := n%44+3) (by omega)]
  have hlt : n % 44 < 44 := Nat.mod_lt n (by omega)
  set r := n % 44 with hr
  interval_cases r <;> decide

/-- when `Wn n > 0`, the atom `Tn n` is 0. -/
lemma Tn_zero_of_Wn_pos (n : Nat) (h : Wn n ≠ 0) : Tn n = 0 := by
  have hb := checkerB_ok
  unfold checkerB at hb
  simp only [Bool.and_eq_true] at hb
  rcases Nat.lt_or_ge n 44 with hn | hn
  · have hread := hb.1.2
    rw [List.all_eq_true] at hread
    have hc := hread n (List.mem_range.mpr (by omega))
    rw [if_neg (by simpa using h)] at hc
    rw [Bool.and_eq_true] at hc
    exact beq_iff_eq.mp hc.2
  · rw [Tn_congr (a := n) (b := n % 44) (by omega)]
    rw [Wn_congr (a := n) (b := n % 44) (by omega)] at h
    have hb2 := hb.1.2
    rw [List.all_eq_true] at hb2
    have hc := hb2 (n % 44) (List.mem_range.mpr (by omega))
    rw [if_neg (by simpa using h)] at hc
    rw [Bool.and_eq_true] at hc
    exact beq_iff_eq.mp hc.2

/-! ### Structural facts about `buildJetsL` (prefix-stability, recurrence) -/

lemma buildJetsL_succ (k : Nat) :
    buildJetsL (k+1) =
      (let Uok := buildJetsL k
       let jb := stepC (fun i => Uok.1.getD i ⟨[], 1⟩) k
       (Uok.1 ++ [jb.1], Uok.2 && jb.2)) := by
  unfold buildJetsL
  rw [List.range_succ, List.foldl_append]
  rfl

lemma buildJetsL_len (k : Nat) : (buildJetsL k).1.length = 4 + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [buildJetsL_succ]; simp only [List.length_append, List.length_cons,
      List.length_nil, ih]; omega

lemma buildJetsL_getD_stable (k n : Nat) (h : n < 4 + k) (d : JetP) :
    (buildJetsL (k+1)).1.getD n d = (buildJetsL k).1.getD n d := by
  rw [buildJetsL_succ]
  show ((buildJetsL k).1 ++ _).getD n d = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [buildJetsL_len]; exact h)]

lemma buildJetsL_getD_mono (n : Nat) (d : JetP) :
    ∀ K k, k ≤ K → n < 4 + k → (buildJetsL K).1.getD n d = (buildJetsL k).1.getD n d := by
  intro K
  induction K with
  | zero => intro k hk _; have : k = 0 := Nat.le_zero.mp hk; subst this; rfl
  | succ K ih =>
    intro k hk hn
    rcases Nat.lt_or_ge k (K+1) with hlt | hge
    · have hkK : k ≤ K := by omega
      rw [buildJetsL_getD_stable K n (by omega) d, ih k hkK hn]
    · have hkeq : k = K + 1 := by omega
      rw [hkeq]

lemma stepC_congr (f g : Nat → JetP) (n : Nat)
    (h1 : f (n+1) = g (n+1)) (h2 : f (n+2) = g (n+2)) (h3 : f (n+3) = g (n+3)) (h0 : f n = g n) :
    stepC f n = stepC g n := by
  unfold stepC
  simp only [h1, h2, h3, h0]

lemma jet_base0 : jet 0 = ⟨Uinit 0, 34⟩ := by
  unfold jet; rw [buildJetsL_getD_mono 0 ⟨[], 1⟩ 44 0 (by omega) (by omega)]; rfl
lemma jet_base1 : jet 1 = ⟨Uinit 1, 34⟩ := by
  unfold jet; rw [buildJetsL_getD_mono 1 ⟨[], 1⟩ 44 0 (by omega) (by omega)]; rfl
lemma jet_base2 : jet 2 = ⟨Uinit 2, 34⟩ := by
  unfold jet; rw [buildJetsL_getD_mono 2 ⟨[], 1⟩ 44 0 (by omega) (by omega)]; rfl
lemma jet_base3 : jet 3 = ⟨Uinit 3, 34⟩ := by
  unfold jet; rw [buildJetsL_getD_mono 3 ⟨[], 1⟩ 44 0 (by omega) (by omega)]; rfl

/-- the jet recurrence: `jet (n+4)` is the step applied to the four previous jets. -/
lemma jet_rec (n : Nat) (h : n < 44) : jet (n+4) = (stepC jet n).1 := by
  have hmono : jet (n+4) = (buildJetsL (n+1)).1.getD (n+4) ⟨[], 1⟩ := by
    unfold jet
    rw [buildJetsL_getD_mono (n+4) ⟨[], 1⟩ 44 (n+1) (by omega) (by omega)]
  rw [hmono, buildJetsL_succ]
  show ((buildJetsL n).1 ++ [_]).getD (n+4) ⟨[], 1⟩ = (stepC jet n).1
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [buildJetsL_len]; omega), buildJetsL_len]
  have h0 : n + 4 - (4 + n) = 0 := by omega
  rw [h0]
  show (stepC (fun i => (buildJetsL n).1.getD i ⟨[], 1⟩) n).1 = (stepC jet n).1
  rw [stepC_congr _ jet n]
  · exact (buildJetsL_getD_mono (n+1) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
  · exact (buildJetsL_getD_mono (n+2) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
  · exact (buildJetsL_getD_mono (n+3) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
  · exact (buildJetsL_getD_mono n ⟨[], 1⟩ 44 n (by omega) (by omega)).symm

lemma buildJetsL_snd (k : Nat) :
    (buildJetsL (k+1)).2 =
      ((buildJetsL k).2 && (stepC (fun i => (buildJetsL k).1.getD i ⟨[], 1⟩) k).2) := by
  conv_lhs => rw [buildJetsL_succ]

/-- `jet` at index `n` uses the same step whether indexed by `buildJetsL n` or `jet`. -/
lemma stepC_jet (n : Nat) (h : n < 44) :
    stepC (fun i => (buildJetsL n).1.getD i ⟨[], 1⟩) n = stepC jet n :=
  stepC_congr _ jet n
    (buildJetsL_getD_mono (n+1) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
    (buildJetsL_getD_mono (n+2) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
    (buildJetsL_getD_mono (n+3) ⟨[], 1⟩ 44 n (by omega) (by omega)).symm
    (buildJetsL_getD_mono n ⟨[], 1⟩ 44 n (by omega) (by omega)).symm

lemma step_ok_aux : ∀ K, K ≤ 44 → (buildJetsL K).2 = true → ∀ n, n < K → (stepC jet n).2 = true := by
  intro K
  induction K with
  | zero => intro _ _ n hn; omega
  | succ K ih =>
    intro hK hsnd n hn
    rw [buildJetsL_snd, Bool.and_eq_true] at hsnd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih (by omega) hsnd.1 n hlt
    · subst heq; rw [← stepC_jet n (by omega)]; exact hsnd.2

lemma buildJetsL44_ok : (buildJetsL 44).2 = true := by
  have h := checkerB_ok
  unfold checkerB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

lemma step_ok (n : Nat) (h : n < 44) : (stepC jet n).2 = true :=
  step_ok_aux 44 (_root_.le_refl 44) buildJetsL44_ok n h

lemma reading_ok (n : Nat) (h : n < 48) (hw : Wn n = 0) :
    Tn n < (jet n).prec ∧ dvdExact (Tn n) (1 + cc (jet n).poly) = true ∧
      ndiv (Tn n + 1) (jet n).poly = true := by
  have hb := checkerB_ok
  unfold checkerB at hb
  simp only [Bool.and_eq_true] at hb
  have hread := hb.1.2
  rw [List.all_eq_true] at hread
  have hn := hread n (List.mem_range.mpr h)
  rw [if_pos (beq_iff_eq.mpr hw)] at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact ⟨hn.2.1.1, hn.2.1.2, hn.2.2⟩

/-- every jet up to index 47 carries precision ≥ 1. -/
lemma prec_pos (n : Nat) (h : n < 48) : 1 ≤ (jet n).prec := by
  have hb := checkerB_ok
  unfold checkerB at hb
  simp only [Bool.and_eq_true] at hb
  have hread := hb.1.2
  rw [List.all_eq_true] at hread
  have hn := hread n (List.mem_range.mpr h)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact hn.1

/-- the factor precision `prec + Wn − Tn` is at least 1. -/
lemma prec_gt (m : Nat) (h : m < 48) : Tn m < (jet m).prec + Wn m := by
  by_cases hw : Wn m = 0
  · obtain ⟨hprec, _, _⟩ := reading_ok m h hw; rw [hw]; omega
  · have hz := Tn_zero_of_Wn_pos m hw
    have hp := prec_pos m h
    rw [hz]; omega

/-! ### Evaluation of the jet operations -/

lemma peval_pscale (s : Nat) (P : Poly) (c) : peval (pscale s P) c = (2^s : ℚ) * peval P c := by
  unfold pscale
  induction P with
  | nil => simp [peval]
  | cons t P ih => simp only [List.map_cons, peval_cons, ih]; push_cast; ring

lemma peval_pconst (x : Int) (c) : peval (pconst x) c = (x : ℚ) := by
  unfold pconst
  split
  · rename_i h; simp only [beq_iff_eq] at h; simp [peval, h]
  · simp [peval_cons, peval_nil, monEval, mon0]

lemma peval_padd_close (p : Nat) (P Q : Poly) {c} (hc : Tube c) :
    Close (p : ℤ) (peval (padd p P Q) c) (peval P c + peval Q c) := by
  unfold padd
  have h := peval_normS_close p (P ++ Q) hc
  rw [peval_append] at h
  exact h

lemma peval_pmul_close (p : Nat) (P Q : Poly) {c} (hc : Tube c) :
    Close (p : ℤ) (peval (pmul p P Q) c) (peval P c * peval Q c) := by
  unfold pmul
  have h := peval_normS_close p
    (P.flatMap (fun (a, x) => Q.map (fun (b, y) => (monMul a b, x * y)))) hc
  rw [peval_flatMul] at h
  exact h

lemma allDiv_dvd {q s : Nat} {P : Poly} (h : allDiv q s P = true) (hsq : s ≤ q) :
    ∀ t ∈ P, (2 ^ s : Int) ∣ t.2 := by
  intro t ht
  unfold allDiv at h
  rw [List.all_eq_true] at h
  have h1 := h t ht
  simp only [beq_iff_eq] at h1
  -- h1 : t.2 % 2^q % 2^s = 0
  have hdvd_q : (2 ^ s : Int) ∣ 2 ^ q := pow_dvd_pow 2 hsq
  have e1 : (2 ^ s : Int) ∣ t.2 % 2 ^ q := Int.dvd_of_emod_eq_zero h1
  have e2 : t.2 % 2 ^ q = t.2 - 2 ^ q * (t.2 / 2 ^ q) := by
    have := Int.mul_ediv_add_emod t.2 (2 ^ q); linarith
  rw [e2] at e1
  have e3 : (2 ^ s : Int) ∣ 2 ^ q * (t.2 / 2 ^ q) := Dvd.dvd.mul_right hdvd_q _
  have := dvd_add e1 e3
  simpa using this

lemma peval_pdiv2 (s : Nat) (P : Poly) (c) (hdiv : ∀ t ∈ P, (2 ^ s : Int) ∣ t.2) :
    peval (pdiv2 s P) c = peval P c / (2 ^ s : ℚ) := by
  unfold pdiv2
  induction P with
  | nil => simp [peval]
  | cons t P ih =>
    have hd : (2 ^ s : Int) ∣ t.2 := hdiv t (List.mem_cons.mpr (Or.inl rfl))
    have ihP := ih (fun u hu => hdiv u (List.mem_cons.mpr (Or.inr hu)))
    simp only [List.map_cons, peval_cons, ihP]
    obtain ⟨k, hk⟩ := hd
    rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
    push_cast
    field_simp

/-! ### Constant term and deep (non-constant) parts -/

lemma monEval_mon0 (c) : monEval mon0 c = 1 := by simp [monEval, mon0]

lemma cc_cons (t : Mon × Int) (P : Poly) :
    cc (t :: P) = (if t.1 == mon0 then t.2 else 0) + cc P := by
  unfold cc; simp only [List.filter_cons]
  split <;> simp [List.sum_cons]

lemma peval_split (P : Poly) (c) :
    peval P c = (cc P : ℚ) + peval (P.filter (fun t => t.1 != mon0)) c := by
  induction P with
  | nil => simp [peval, cc]
  | cons t P ih =>
    by_cases h : (t.1 == mon0) = true
    · have hfil : (t :: P).filter (fun t => t.1 != mon0) = P.filter (fun t => t.1 != mon0) := by
        rw [List.filter_cons]; simp [bne, h]
      have hmon : monEval t.1 c = 1 := by rw [beq_iff_eq.mp h, monEval_mon0]
      rw [peval_cons, hfil, cc_cons, if_pos h, hmon, ih]; push_cast; ring
    · have hfil : (t :: P).filter (fun t => t.1 != mon0) = t :: P.filter (fun t => t.1 != mon0) := by
        rw [List.filter_cons]; simp [bne, h]
      rw [peval_cons, hfil, cc_cons, if_neg h, peval_cons, ih]; push_cast; ring

/-- valuation lower bound of a poly whose coefficients are all divisible by `2^m`. -/
lemma peval_deep (m : Nat) (P : Poly) {c} (hc : Tube c) (hdvd : ∀ t ∈ P, (2 ^ m : Int) ∣ t.2) :
    peval P c = 0 ∨ (m : ℤ) ≤ padicValRat 2 (peval P c) := by
  have hpd := peval_pdiv2 m P c hdvd
  have hP : peval P c = (2 ^ m : ℚ) * peval (pdiv2 m P) c := by
    rw [hpd]; field_simp
  rcases eq_or_ne (peval (pdiv2 m P) c) 0 with hz | hz
  · left; rw [hP, hz]; ring
  · right
    have hI := (peval_Int2 hc (pdiv2 m P)).resolve_left hz
    rw [hP, padicValRat.mul (by positivity) hz, v2_two_pow]; omega

lemma ndiv_dvd {m : Nat} {P : Poly} (h : ndiv m P = true) :
    ∀ t ∈ P, t.1 ≠ mon0 → (2 ^ m : Int) ∣ t.2 := by
  intro t ht hne
  unfold ndiv at h
  rw [List.all_eq_true] at h
  have hmem : t ∈ P.filter (fun t => t.1 != mon0) :=
    List.mem_filter.mpr ⟨ht, by simp [bne_iff_ne, hne]⟩
  have := h t hmem
  simp only [beq_iff_eq] at this
  exact Int.dvd_of_emod_eq_zero this

/-- on the tube, `peval P` is 2-adically `m`-close to its constant term. -/
lemma peval_close_cc {m : Nat} {P : Poly} {c} (hc : Tube c) (h : ndiv m P = true) :
    Close (m : ℤ) (peval P c) (cc P : ℚ) := by
  have hdeep : peval (P.filter (fun t => t.1 != mon0)) c = 0 ∨
      (m : ℤ) ≤ padicValRat 2 (peval (P.filter (fun t => t.1 != mon0)) c) := by
    apply peval_deep m _ hc
    intro t ht
    rw [List.mem_filter] at ht
    exact ndiv_dvd h t ht.1 (by simpa [bne_iff_ne] using ht.2)
  rw [peval_split P c]
  rcases hdeep with hz | hv
  · left; rw [hz]; ring
  · right
    rw [show (↑(cc P) + peval (P.filter (fun t => t.1 != mon0)) c) - (↑(cc P) : ℚ)
        = peval (P.filter (fun t => t.1 != mon0)) c by ring]
    exact hv

/-- `dvdExact m x` pins the 2-adic valuation of `x` to `m`. -/
lemma dvdExact_padicVal {m : Nat} {x : Int} (h : dvdExact m x = true) :
    x ≠ 0 ∧ padicValRat 2 (x : ℚ) = m := by
  unfold dvdExact at h
  rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hdvd : (2 ^ m : Int) ∣ x := Int.dvd_of_emod_eq_zero h1
  have hndvd : ¬ (2 ^ (m+1) : Int) ∣ x := fun hd => h2 (Int.emod_eq_zero_of_dvd hd)
  obtain ⟨k, hk⟩ := hdvd
  have hxne : x ≠ 0 := by rintro rfl; exact hndvd (dvd_zero _)
  have hkodd : ¬ (2 : Int) ∣ k := by
    rintro ⟨j, rfl⟩; exact hndvd ⟨j, by rw [hk]; ring⟩
  have hkne : k ≠ 0 := by rintro rfl; exact hxne (by rw [hk]; ring)
  refine ⟨hxne, ?_⟩
  rw [hk]; push_cast
  rw [padicValRat.mul (by positivity) (by exact_mod_cast hkne), v2_two_pow]
  have hk0 : padicValRat 2 (k : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hkodd
  rw [hk0]; ring

/-- the per-factor valuation reading: `v₂(1 + seqₘ) = Tₘ`, and `1 + seqₘ ≠ 0`. -/
lemma val_one_add {c : Fin 4 → ℚ} (hc : Tube c) (m : Nat) (h : m < 48)
    (hrep : Rep c m (jet m).poly (jet m).prec) :
    1 + seq (win c) m ≠ 0 ∧ padicValRat 2 (1 + seq (win c) m) = (Tn m : ℤ) := by
  obtain ⟨hne, hval, hclose⟩ := hrep
  by_cases hw : Wn m = 0
  · obtain ⟨hprec, hdvd, hnd⟩ := reading_ok m h hw
    rw [hw, pow_zero, div_one] at hclose
    obtain ⟨hccne, hccval⟩ := dvdExact_padicVal hdvd
    have hcc := peval_close_cc hc hnd
    have hle : ((Tn m : ℤ) + 1) ≤ ((jet m).prec : ℤ) := by exact_mod_cast hprec
    have hchain : Close ((Tn m : ℤ) + 1) (seq (win c) m) ((cc (jet m).poly : Int) : ℚ) := by
      have h1 : Close ((Tn m : ℤ) + 1) (seq (win c) m) (peval (jet m).poly c) :=
        hclose.mono hle
      have h2 : Close ((Tn m : ℤ) + 1) (peval (jet m).poly c) ((cc (jet m).poly : Int) : ℚ) := by
        have := hcc; push_cast at this ⊢; exact this
      exact h1.trans h2
    have hadd : Close ((Tn m : ℤ) + 1) (1 + seq (win c) m) (1 + (cc (jet m).poly : ℚ)) := by
      have := hchain.add_left 1; push_cast at this ⊢; exact this
    have hXne : (1 + (cc (jet m).poly : ℚ)) ≠ 0 := by
      have : ((1 + cc (jet m).poly : Int) : ℚ) ≠ 0 := by exact_mod_cast hccne
      push_cast at this; exact this
    have hXval : padicValRat 2 (1 + (cc (jet m).poly : ℚ)) = (Tn m : ℤ) := by
      have := hccval; push_cast at this ⊢; exact this
    exact hadd.val_eq hXne hXval (by omega)
  · have htn : Tn m = 0 := Tn_zero_of_Wn_pos m hw
    have hwpos : (1 : ℤ) ≤ (Wn m : ℤ) := by omega
    have hclose1 : Close 1 (1 + seq (win c) m) 1 := by
      right
      rw [show 1 + seq (win c) m - 1 = seq (win c) m by ring, hval]
      exact hwpos
    obtain ⟨hx, hv⟩ := hclose1.val_eq one_ne_zero padicValRat.one (by norm_num)
    exact ⟨hx, by rw [htn]; exact_mod_cast hv⟩

/-- valuation half of step-preservation: `v₂(seq(n+4)) = Wn(n+4)`. -/
lemma val_seq_step {c : Fin 4 → ℚ} (hc : Tube c) (n : Nat) (h : n + 3 < 48)
    (r0 : Rep c n (jet n).poly (jet n).prec)
    (r1 : Rep c (n+1) (jet (n+1)).poly (jet (n+1)).prec)
    (r2 : Rep c (n+2) (jet (n+2)).poly (jet (n+2)).prec)
    (r3 : Rep c (n+3) (jet (n+3)).poly (jet (n+3)).prec) :
    seq (win c) (n+4) ≠ 0 ∧ padicValRat 2 (seq (win c) (n+4)) = (Wn (n+4) : ℤ) := by
  obtain ⟨h1ne, h1v⟩ := val_one_add hc (n+1) (by omega) r1
  obtain ⟨h2ne, h2v⟩ := val_one_add hc (n+2) (by omega) r2
  obtain ⟨h3ne, h3v⟩ := val_one_add hc (n+3) (by omega) r3
  have hs0 : seq (win c) n ≠ 0 := r0.1
  have hv0 : padicValRat 2 (seq (win c) n) = (Wn n : ℤ) := r0.2.1
  have b1 : seq (win c) (n+1) + 1 ≠ 0 := by rw [add_comm]; exact h1ne
  have b2 : seq (win c) (n+2) + 1 ≠ 0 := by rw [add_comm]; exact h2ne
  have b3 : seq (win c) (n+3) + 1 ≠ 0 := by rw [add_comm]; exact h3ne
  have hrec : seq (win c) (n+4)
      = (seq (win c) (n+3) + 1) * (seq (win c) (n+2) + 1) * (seq (win c) (n+1) + 1)
        / seq (win c) n := rfl
  refine ⟨by rw [hrec]; exact div_ne_zero (mul_ne_zero (mul_ne_zero b3 b2) b1) hs0, ?_⟩
  rw [hrec, padicValRat.div (mul_ne_zero (mul_ne_zero b3 b2) b1) hs0,
      padicValRat.mul (mul_ne_zero b3 b2) b1, padicValRat.mul b3 b2,
      show seq (win c) (n+3) + 1 = 1 + seq (win c) (n+3) from by ring,
      show seq (win c) (n+2) + 1 = 1 + seq (win c) (n+2) from by ring,
      show seq (win c) (n+1) + 1 = 1 + seq (win c) (n+1) from by ring,
      h1v, h2v, h3v, hv0]
  have hb := balance n
  omega

lemma Close.symm {k : ℤ} {x y : ℚ} (h : Close k x y) : Close k y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right; rwa [show y - x = -(x - y) by ring, padicValRat.neg]

lemma Close.div2 {k : ℤ} {x y : ℚ} (α : ℕ) (h : Close k x y) :
    Close (k - α) (x / 2 ^ α) (y / 2 ^ α) := by
  rcases h.cases' with rfl | ⟨hn, hv⟩
  · exact Close.refl _ _
  · right
    rw [show x / 2 ^ α - y / 2 ^ α = (x - y) / 2 ^ α by ring,
      padicValRat.div hn (by positivity), v2_two_pow]
    omega

/-- per-factor closeness: `peval fⱼ ≈ (1 + seqₘ)/2^{Tₘ}`. -/
lemma factor_close {c : Fin 4 → ℚ} (hc : Tube c) (m : Nat)
    (hrep : Rep c m (jet m).poly (jet m).prec)
    (hTle : (Tn m : ℤ) ≤ (jet m).prec + Wn m)
    (hdiv : allDiv ((jet m).prec + Wn m) (Tn m)
      (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1)) = true) :
    Close (((jet m).prec : ℤ) + Wn m - Tn m) ((1 + seq (win c) m) / 2 ^ Tn m)
      (peval (pdiv2 (Tn m)
        (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1))) c) := by
  obtain ⟨hne, hval, hclose⟩ := hrep
  have hs := hclose.scale (Wn m)
  rw [show (2:ℚ) ^ (Wn m) * (seq (win c) m / 2 ^ (Wn m)) = seq (win c) m by field_simp] at hs
  have hs1 := hs.add_left 1
  have he := peval_padd_close ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1) hc
  rw [peval_pscale, peval_pconst] at he
  have hchain : Close ((jet m).prec + Wn m : ℤ) (1 + seq (win c) m)
      (peval (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1)) c) := by
    rw [show (1:ℚ) + 2 ^ (Wn m) * peval (jet m).poly c
        = 2 ^ (Wn m) * peval (jet m).poly c + 1 from by ring] at hs1
    have : Close (((jet m).prec : ℤ) + Wn m) (1 + seq (win c) m)
        (peval (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1)) c) := by
      refine hs1.trans (Close.symm ?_)
      have := he; push_cast at this ⊢; convert this using 2
    exact this
  have hpd : peval (pdiv2 (Tn m)
        (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1))) c
      = peval (padd ((jet m).prec + Wn m) (pscale (Wn m) (jet m).poly) (pconst 1)) c / 2 ^ Tn m := by
    apply peval_pdiv2
    exact allDiv_dvd hdiv (by exact_mod_cast hTle)
  rw [hpd]
  have hd := hchain.div2 (Tn m)
  convert hd using 2

lemma Close.mul_right {k : ℤ} {x y : ℚ} (z : ℚ) (hz : z ≠ 0) (hzv : 0 ≤ padicValRat 2 z)
    (h : Close k x y) : Close k (x * z) (y * z) := by
  rcases h.cases' with rfl | ⟨hn, hv⟩
  · exact Close.refl _ _
  · right; rw [show x * z - y * z = (x - y) * z by ring, padicValRat.mul hn hz]; omega

/-- inverse closeness: from the Newton witness, `peval inv ≈ (peval P₀)⁻¹`. -/
lemma inv_close {c : Fin 4 → ℚ} (hc : Tube c) (pd : Nat) (P0 inv : Poly)
    (hwit : pmul pd P0 inv = pconst 1) (h0 : peval P0 c ≠ 0) (h0v : padicValRat 2 (peval P0 c) = 0) :
    Close (pd : ℤ) (peval inv c) (peval P0 c)⁻¹ := by
  have hprod : Close (pd : ℤ) (peval P0 c * peval inv c) 1 := by
    have := peval_pmul_close pd P0 inv hc
    rw [hwit, peval_pconst] at this
    simpa using this.symm
  have hstep := hprod.mul_right (peval P0 c)⁻¹ (by positivity) (by
    rw [padicValRat.inv, h0v]; norm_num)
  rw [show peval P0 c * peval inv c * (peval P0 c)⁻¹ = peval inv c by field_simp,
      one_mul] at hstep
  exact hstep

/-! ### `rfl`-handles for the step output -/

/-- the factor precision at phase `n+j`. -/
@[reducible] def fprec (n j : Nat) : Nat := (jet (n+j)).prec + Wn (n+j) - Tn (n+j)
/-- the minimum factor precision over the three phases. -/
@[reducible] def pminOf (n : Nat) : Nat := min (fprec n 1) (min (fprec n 2) (fprec n 3))
/-- the `1 + 2^w U` expression at phase `n+j`. -/
@[reducible] def Eexpr (n j : Nat) : Poly :=
  padd ((jet (n+j)).prec + Wn (n+j)) (pscale (Wn (n+j)) (jet (n+j)).poly) (pconst 1)
/-- the factor expression at phase `n+j`. -/
@[reducible] def Fexpr (n j : Nat) : Poly := pdiv2 (Tn (n+j)) (Eexpr n j)

lemma stepC_fst_prec (n : Nat) : (stepC jet n).1.prec = min (pminOf n) (jet n).prec := rfl

/-- the step-validity boolean, expanded. -/
lemma stepC_snd (n : Nat) :
    (stepC jet n).2 =
      ((allDiv ((jet (n+1)).prec + Wn (n+1)) (Tn (n+1)) (Eexpr n 1)
          && (cc (Fexpr n 1) % 2 == 1) && ndiv 1 (Fexpr n 1))
       && (allDiv ((jet (n+2)).prec + Wn (n+2)) (Tn (n+2)) (Eexpr n 2)
          && (cc (Fexpr n 2) % 2 == 1) && ndiv 1 (Fexpr n 2))
       && (allDiv ((jet (n+3)).prec + Wn (n+3)) (Tn (n+3)) (Eexpr n 3)
          && (cc (Fexpr n 3) % 2 == 1) && ndiv 1 (Fexpr n 3))
       && (pmul (min (pminOf n) (jet n).prec) (jet n).poly
            (pinv (min (pminOf n) (jet n).prec) (jet n).poly) == pconst 1)) := rfl

lemma stepC_fst_poly (n : Nat) :
    (stepC jet n).1.poly =
      pmul (min (pminOf n) (jet n).prec)
        (pmul (pminOf n) (pmul (pminOf n) (Fexpr n 1) (Fexpr n 2)) (Fexpr n 3))
        (pinv (min (pminOf n) (jet n).prec) (jet n).poly) := rfl

/-- exact identity: the unit at `n+4` equals `∏ Hⱼ · U₀⁻¹`. -/
lemma seq_step_eq {c : Fin 4 → ℚ} (n : Nat) (hs0 : seq (win c) n ≠ 0) :
    seq (win c) (n+4) / 2 ^ (Wn (n+4))
      = (1 + seq (win c) (n+1)) / 2 ^ (Tn (n+1))
        * ((1 + seq (win c) (n+2)) / 2 ^ (Tn (n+2)))
        * ((1 + seq (win c) (n+3)) / 2 ^ (Tn (n+3)))
        * (seq (win c) n / 2 ^ (Wn n))⁻¹ := by
  have hrec : seq (win c) (n+4)
      = (seq (win c) (n+3) + 1) * (seq (win c) (n+2) + 1) * (seq (win c) (n+1) + 1)
        / seq (win c) n := rfl
  have hbN : Wn (n+4) + Wn n = Tn (n+1) + Tn (n+2) + Tn (n+3) := by
    have := balance n; omega
  have hpow : (2:ℚ) ^ (Wn (n+4)) * 2 ^ (Wn n)
      = 2 ^ (Tn (n+1)) * (2 ^ (Tn (n+2)) * 2 ^ (Tn (n+3))) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [hrec]
  field_simp
  linear_combination
    (-(seq (win c) (n + 3) + 1) * (seq (win c) (n + 2) + 1) * (seq (win c) (n + 1) + 1)) * hpow

/-- **step preservation**: from `Rep` at `n, n+1, n+2, n+3` derive `Rep` at `n+4`. -/
lemma step_prep {c : Fin 4 → ℚ} (hc : Tube c) (n : Nat) (h : n < 44)
    (r0 : Rep c n (jet n).poly (jet n).prec)
    (r1 : Rep c (n+1) (jet (n+1)).poly (jet (n+1)).prec)
    (r2 : Rep c (n+2) (jet (n+2)).poly (jet (n+2)).prec)
    (r3 : Rep c (n+3) (jet (n+3)).poly (jet (n+3)).prec) :
    Rep c (n+4) (jet (n+4)).poly (jet (n+4)).prec := by
  obtain ⟨hne4, hval4⟩ := val_seq_step hc n (by omega) r0 r1 r2 r3
  refine ⟨hne4, hval4, ?_⟩
  -- rewrite the jet at n+4 into the step output
  have hprec4 : (jet (n+4)).prec = min (pminOf n) (jet n).prec := by
    rw [jet_rec n h, stepC_fst_prec]
  have hpoly4 : (jet (n+4)).poly =
      pmul (min (pminOf n) (jet n).prec)
        (pmul (pminOf n) (pmul (pminOf n) (Fexpr n 1) (Fexpr n 2)) (Fexpr n 3))
        (pinv (min (pminOf n) (jet n).prec) (jet n).poly) := by
    rw [jet_rec n h, stepC_fst_poly]
  rw [hprec4, hpoly4]
  -- extract the per-step validity facts
  have hstep := step_ok n h
  rw [stepC_snd] at hstep
  simp only [Bool.and_eq_true] at hstep
  obtain ⟨⟨⟨⟨⟨hdiv1, _⟩, _⟩, ⟨⟨hdiv2, _⟩, _⟩⟩, ⟨⟨hdiv3, _⟩, _⟩⟩, hwiteq⟩ := hstep
  have hwit : pmul (min (pminOf n) (jet n).prec) (jet n).poly
      (pinv (min (pminOf n) (jet n).prec) (jet n).poly) = pconst 1 := beq_iff_eq.mp hwiteq
  -- name the pieces
  set pm := pminOf n with hpm
  set pd := min pm (jet n).prec with hpd
  set inv := pinv pd (jet n).poly with hinv
  set F1 := Fexpr n 1 with hF1
  set F2 := Fexpr n 2 with hF2
  set F3 := Fexpr n 3 with hF3
  -- basic positivity of precisions
  have hprec_pos : 1 ≤ (jet n).prec := prec_pos n (by omega)
  have hg1 := prec_gt (n+1) (by omega)
  have hg2 := prec_gt (n+2) (by omega)
  have hg3 := prec_gt (n+3) (by omega)
  have hfp1 : 1 ≤ fprec n 1 := by unfold fprec; omega
  have hfp2 : 1 ≤ fprec n 2 := by unfold fprec; omega
  have hfp3 : 1 ≤ fprec n 3 := by unfold fprec; omega
  have hpm_pos : 1 ≤ pm := by
    rw [hpm]; exact _root_.le_min_iff.mpr ⟨hfp1, _root_.le_min_iff.mpr ⟨hfp2, hfp3⟩⟩
  have hpd_pos : 1 ≤ pd := by
    rw [hpd]; exact _root_.le_min_iff.mpr ⟨hpm_pos, hprec_pos⟩
  have hpd_pm : pd ≤ pm := by rw [hpd]; exact Nat.min_le_left _ _
  have hpd_prec : pd ≤ (jet n).prec := by rw [hpd]; exact Nat.min_le_right _ _
  have hpm_f1 : pm ≤ (jet (n+1)).prec + Wn (n+1) - Tn (n+1) := by
    rw [hpm]; exact Nat.min_le_left _ _
  have hpm_f2 : pm ≤ (jet (n+2)).prec + Wn (n+2) - Tn (n+2) := by
    rw [hpm]; exact _root_.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have hpm_f3 : pm ≤ (jet (n+3)).prec + Wn (n+3) - Tn (n+3) := by
    rw [hpm]; exact _root_.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
  -- destructure the base representation
  obtain ⟨hs0, hsv0, hclose0⟩ := r0
  -- the base unit S = seq n / 2^{Wn n}
  have hSne : seq (win c) n / 2 ^ (Wn n) ≠ 0 := div_ne_zero hs0 (by positivity)
  have hSv : padicValRat 2 (seq (win c) n / 2 ^ (Wn n)) = 0 := by
    rw [padicValRat.div hs0 (by positivity), hsv0, v2_two_pow]; ring
  have hSinvne : (seq (win c) n / 2 ^ (Wn n))⁻¹ ≠ 0 := inv_ne_zero hSne
  have hSinvv : padicValRat 2 (seq (win c) n / 2 ^ (Wn n))⁻¹ = 0 := by
    rw [padicValRat.inv, hSv]; ring
  -- U_n(c) is a unit
  obtain ⟨hP0ne, hP0v⟩ := (hclose0.symm).val_eq hSne hSv (by omega)
  -- the three H-factors are units
  obtain ⟨h1ne, h1v⟩ := val_one_add hc (n+1) (by omega) r1
  obtain ⟨h2ne, h2v⟩ := val_one_add hc (n+2) (by omega) r2
  obtain ⟨h3ne, h3v⟩ := val_one_add hc (n+3) (by omega) r3
  have hH1ne : (1 + seq (win c) (n+1)) / 2 ^ (Tn (n+1)) ≠ 0 := div_ne_zero h1ne (by positivity)
  have hH2ne : (1 + seq (win c) (n+2)) / 2 ^ (Tn (n+2)) ≠ 0 := div_ne_zero h2ne (by positivity)
  have hH3ne : (1 + seq (win c) (n+3)) / 2 ^ (Tn (n+3)) ≠ 0 := div_ne_zero h3ne (by positivity)
  have hH1v : padicValRat 2 ((1 + seq (win c) (n+1)) / 2 ^ (Tn (n+1))) = 0 := by
    rw [padicValRat.div h1ne (by positivity), h1v, v2_two_pow]; ring
  have hH2v : padicValRat 2 ((1 + seq (win c) (n+2)) / 2 ^ (Tn (n+2))) = 0 := by
    rw [padicValRat.div h2ne (by positivity), h2v, v2_two_pow]; ring
  have hH3v : padicValRat 2 ((1 + seq (win c) (n+3)) / 2 ^ (Tn (n+3))) = 0 := by
    rw [padicValRat.div h3ne (by positivity), h3v, v2_two_pow]; ring
  -- per-factor closeness, moved to precision pd
  have hf1 : Close (pd : ℤ) ((1 + seq (win c) (n+1)) / 2 ^ (Tn (n+1))) (peval F1 c) :=
    (factor_close hc (n+1) r1 (by omega) hdiv1).mono (by omega)
  have hf2 : Close (pd : ℤ) ((1 + seq (win c) (n+2)) / 2 ^ (Tn (n+2))) (peval F2 c) :=
    (factor_close hc (n+2) r2 (by omega) hdiv2).mono (by omega)
  have hf3 : Close (pd : ℤ) ((1 + seq (win c) (n+3)) / 2 ^ (Tn (n+3))) (peval F3 c) :=
    (factor_close hc (n+3) r3 (by omega) hdiv3).mono (by omega)
  -- the poly factors are units
  obtain ⟨hpF1ne, hpF1v⟩ := (hf1.symm).val_eq hH1ne hH1v (by omega)
  obtain ⟨hpF2ne, hpF2v⟩ := (hf2.symm).val_eq hH2ne hH2v (by omega)
  obtain ⟨hpF3ne, hpF3v⟩ := (hf3.symm).val_eq hH3ne hH3v (by omega)
  -- the inverse
  have hinvclose : Close (pd : ℤ) (peval inv c) (peval (jet n).poly c)⁻¹ :=
    inv_close hc pd (jet n).poly inv hwit hP0ne hP0v
  have hP0inv : Close ((jet n).prec : ℤ) (seq (win c) n / 2 ^ (Wn n))⁻¹ (peval (jet n).poly c)⁻¹ :=
    hclose0.inv hSne hP0ne hSv hP0v
  have hSinv : Close (pd : ℤ) (seq (win c) n / 2 ^ (Wn n))⁻¹ (peval inv c) :=
    (hP0inv.mono (by exact_mod_cast hpd_prec)).trans hinvclose.symm
  obtain ⟨hInvne, hInvv⟩ := (hSinv.symm).val_eq hSinvne hSinvv (by omega)
  -- rewrite the goal's numerator via the exact identity
  rw [seq_step_eq n hs0]
  set H1 := (1 + seq (win c) (n+1)) / 2 ^ (Tn (n+1)) with hH1d
  set H2 := (1 + seq (win c) (n+2)) / 2 ^ (Tn (n+2)) with hH2d
  set H3 := (1 + seq (win c) (n+3)) / 2 ^ (Tn (n+3)) with hH3d
  set S := seq (win c) n / 2 ^ (Wn n) with hSd
  -- combine the three factors and the inverse
  have hH12v : padicValRat 2 (H1 * H2) = 0 := by
    rw [padicValRat.mul hH1ne hH2ne, hH1v, hH2v]; ring
  have hH123v : padicValRat 2 (H1 * H2 * H3) = 0 := by
    rw [padicValRat.mul (mul_ne_zero hH1ne hH2ne) hH3ne, hH12v, hH3v]; ring
  have hM12 : Close (pd : ℤ) (H1 * H2) (peval F1 c * peval F2 c) :=
    Close.mul hH1ne (_root_.le_of_eq hH1v.symm) hpF2ne (_root_.le_of_eq hpF2v.symm) hf1 hf2
  have hM123 : Close (pd : ℤ) (H1 * H2 * H3) (peval F1 c * peval F2 c * peval F3 c) :=
    Close.mul (mul_ne_zero hH1ne hH2ne) (_root_.le_of_eq hH12v.symm) hpF3ne (_root_.le_of_eq hpF3v.symm) hM12 hf3
  have hMfull : Close (pd : ℤ) (H1 * H2 * H3 * S⁻¹)
      (peval F1 c * peval F2 c * peval F3 c * peval inv c) :=
    Close.mul (mul_ne_zero (mul_ne_zero hH1ne hH2ne) hH3ne) (_root_.le_of_eq hH123v.symm)
      hInvne (_root_.le_of_eq hInvv.symm) hM123 hSinv
  -- the polynomial numerator evaluates to the product of the factor evaluations
  have hnumerclose : Close (pm : ℤ) (peval (pmul pm (pmul pm F1 F2) F3) c)
      (peval F1 c * peval F2 c * peval F3 c) := by
    have hAB := peval_pmul_close pm (pmul pm F1 F2) F3 hc
    have hF12 := peval_pmul_close pm F1 F2 hc
    exact hAB.trans (hF12.mul_right (peval F3 c) hpF3ne (_root_.le_of_eq hpF3v.symm))
  have hnumerclose' : Close (pd : ℤ) (peval (pmul pm (pmul pm F1 F2) F3) c)
      (peval F1 c * peval F2 c * peval F3 c) := hnumerclose.mono (by exact_mod_cast hpd_pm)
  have hA : Close (pd : ℤ) (peval (pmul pd (pmul pm (pmul pm F1 F2) F3) inv) c)
      (peval (pmul pm (pmul pm F1 F2) F3) c * peval inv c) :=
    peval_pmul_close pd (pmul pm (pmul pm F1 F2) F3) inv hc
  have hRHS : Close (pd : ℤ) (peval (pmul pd (pmul pm (pmul pm F1 F2) F3) inv) c)
      (peval F1 c * peval F2 c * peval F3 c * peval inv c) :=
    hA.trans (hnumerclose'.mul_right (peval inv c) hInvne (_root_.le_of_eq hInvv.symm))
  exact hMfull.trans hRHS.symm

/-! ### The 44-step induction, the return-to-tube, and the block induction -/

/-- reading the return clause of `checkerB`: for `44 ≤ n < 48`, `Uₙ ≡ 1 (mod 16)`. -/
lemma return_read (n : Nat) (h1 : 44 ≤ n) (h2 : n < 48) :
    4 ≤ (jet n).prec ∧ cc (jet n).poly % 16 = 1 ∧ ndiv 4 (jet n).poly = true := by
  have hb := checkerB_ok
  unfold checkerB at hb
  simp only [Bool.and_eq_true] at hb
  have hret := hb.2
  rw [List.all_eq_true] at hret
  have hn := hret n (by interval_cases n <;> decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn
  exact ⟨hn.1.1, hn.1.2, hn.2⟩

/-- the **44-step induction**: every window jet up to index 47 represents `seq`. -/
lemma reps (c : Fin 4 → ℚ) (hc : Tube c) :
    ∀ n, n ≤ 47 → Rep c n (jet n).poly (jet n).prec := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, ih, hn with
    | 0, _, _ => simpa only [jet_base0] using (rep_base c hc 34).1
    | 1, _, _ => simpa only [jet_base1] using (rep_base c hc 34).2.1
    | 2, _, _ => simpa only [jet_base2] using (rep_base c hc 34).2.2.1
    | 3, _, _ => simpa only [jet_base3] using (rep_base c hc 34).2.2.2
    | (m+4), ih, hn =>
      exact step_prep hc m (by omega)
        (ih m (by omega) (by omega)) (ih (m+1) (by omega) (by omega))
        (ih (m+2) (by omega) (by omega)) (ih (m+3) (by omega) (by omega))

/-- `v₂(x) ≥ e` whenever `2^e ∣ x` (or `x = 0`). -/
lemma val_ge_of_dvd {w : Int} {e : Nat} (h : (2 ^ e : Int) ∣ w) :
    w = 0 ∨ (e : ℤ) ≤ padicValRat 2 (w : ℚ) := by
  rcases eq_or_ne w 0 with rfl | hne
  · left; rfl
  · right
    obtain ⟨k, hk⟩ := h
    have hkne : k ≠ 0 := by rintro rfl; simp at hk; exact hne hk
    rw [hk]; push_cast
    rw [padicValRat.mul (by positivity) (by exact_mod_cast hkne), v2_two_pow]
    have : 0 ≤ padicValRat 2 (k : ℚ) := (Int2_intCast k).resolve_left (by exact_mod_cast hkne)
    omega

/-- an integer `≡ 1 (mod 16)` is 2-adically 4-close to `1`. -/
lemma Close4_of_mod16 {z : Int} (h : z % 16 = 1) : Close 4 (z : ℚ) 1 := by
  have hdvd : (2 ^ 4 : Int) ∣ (z - 1) := by
    have h0 : (z - 1) % 16 = 0 := by omega
    have := Int.dvd_of_emod_eq_zero h0; simpa using this
  rcases val_ge_of_dvd hdvd with hz | hv
  · left; have : z = 1 := by omega
    rw [this]; norm_num
  · right
    rw [show (z : ℚ) - 1 = ((z - 1 : Int) : ℚ) by push_cast; ring]
    exact hv

/-- if `x` is 4-close to `1`, then `(x−1)/16` is a 2-adic integer. -/
lemma Int2_of_close4 {x : ℚ} (h : Close 4 x 1) : Int2 ((x - 1) / 16) := by
  rcases h with rfl | hv
  · left; norm_num
  · right
    have hne : x - 1 ≠ 0 := by
      intro he; rw [he] at hv; simp at hv
    rw [show (x - 1) / 16 = (x - 1) / 2 ^ 4 by norm_num,
      padicValRat.div hne (by positivity), v2_two_pow]
    omega

/-- the shifted window recovers the sequence values at `44 + i`. -/
lemma win_shift (c : Fin 4 → ℚ) (i : Fin 4) :
    win (fun j : Fin 4 => (seq (win c) (44 + j.val) - 1) / 16) i = seq (win c) (44 + i.val) := by
  simp only [win]; ring

/-- shift-invariance of `seq`: a window equal to `seq` at `44+i` continues it. -/
lemma seq_offset (c : Fin 4 → ℚ) (w : Fin 4 → ℚ)
    (hw : ∀ i : Fin 4, w i = seq (win c) (44 + i.val)) :
    ∀ k, seq w k = seq (win c) (44 + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => exact hw 0
    | 1, _ => exact hw 1
    | 2, _ => exact hw 2
    | 3, _ => exact hw 3
    | (m+4), ih =>
      have e0 := ih m (by omega)
      have e1 := ih (m+1) (by omega)
      have e2 := ih (m+2) (by omega)
      have e3 := ih (m+3) (by omega)
      have hL : seq w (m+4)
          = (seq w (m+3) + 1) * (seq w (m+2) + 1) * (seq w (m+1) + 1) / seq w m := rfl
      have hR : seq (win c) (44 + (m+4))
          = (seq (win c) (44 + (m+3)) + 1) * (seq (win c) (44 + (m+2)) + 1)
              * (seq (win c) (44 + (m+1)) + 1) / seq (win c) (44 + m) := rfl
      rw [hL, hR, e0, e1, e2, e3]

/-- the window returns to the tube after 44 steps. -/
lemma return_tube (c : Fin 4 → ℚ) (hc : Tube c) :
    Tube (fun i : Fin 4 => (seq (win c) (44 + i.val) - 1) / 16) := by
  intro i
  apply Int2_of_close4
  obtain ⟨hprec, hcc, hnd⟩ := return_read (44 + i.val) (by omega) (by omega)
  obtain ⟨hne, hval, hclose⟩ := reps c hc (44 + i.val) (by omega)
  have hw0 : Wn (44 + i.val) = 0 := by fin_cases i <;> rfl
  rw [hw0, pow_zero, div_one] at hclose
  have hprec4 : (4 : ℤ) ≤ ((jet (44 + i.val)).prec : ℤ) := by exact_mod_cast hprec
  have step1 : Close (4 : ℤ) (seq (win c) (44 + i.val)) (peval (jet (44 + i.val)).poly c) :=
    hclose.mono hprec4
  have step2 : Close (4 : ℤ) (peval (jet (44 + i.val)).poly c)
      ((cc (jet (44 + i.val)).poly : ℚ)) := by
    have := peval_close_cc hc hnd; exact_mod_cast this
  have step3 : Close (4 : ℤ) ((cc (jet (44 + i.val)).poly : ℚ)) 1 := Close4_of_mod16 hcc
  exact (step1.trans step2).trans step3

/-- **Part 2, main conclusion**: on any tube window, every `seq` value is a 2-adic integer. -/
lemma val_nonneg : ∀ n, ∀ c : Fin 4 → ℚ, Tube c → 0 ≤ padicValRat 2 (seq (win c) n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    rcases Nat.lt_or_ge n 44 with hlt | hge
    · have hr := reps c hc n (by omega)
      rw [hr.2.1]; exact_mod_cast Nat.zero_le _
    · have hwin : ∀ i : Fin 4,
          win (fun j : Fin 4 => (seq (win c) (44 + j.val) - 1) / 16) i = seq (win c) (44 + i.val) :=
        win_shift c
      have hoff := seq_offset c _ hwin (n - 44)
      rw [show 44 + (n - 44) = n from by omega] at hoff
      rw [← hoff]
      exact ih (n - 44) (by omega) _ (return_tube c hc)

end Return


/-! ## Connection: `a = seq (win 0)`, and the main theorem -/

/-- the A276175 sequence is the `seq` of the all-zero (centre) tube window. -/
lemma a_eq_seq : ∀ n, A276175.a n = Return.seq (Return.win (fun _ => 0)) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [A276175.a, Return.seq, Return.win]
    | 1, _ => norm_num [A276175.a, Return.seq, Return.win]
    | 2, _ => norm_num [A276175.a, Return.seq, Return.win]
    | 3, _ => norm_num [A276175.a, Return.seq, Return.win]
    | (m+4), ih =>
      have e0 := ih m (by omega)
      have e1 := ih (m+1) (by omega)
      have e2 := ih (m+2) (by omega)
      have e3 := ih (m+3) (by omega)
      have hL : A276175.a (m+4)
          = (A276175.a (m+3) + 1) * (A276175.a (m+2) + 1)
              * (A276175.a (m+1) + 1) / A276175.a m := rfl
      have hR : Return.seq (Return.win (fun _ => 0)) (m+4)
          = (Return.seq (Return.win (fun _ => 0)) (m+3) + 1)
              * (Return.seq (Return.win (fun _ => 0)) (m+2) + 1)
              * (Return.seq (Return.win (fun _ => 0)) (m+1) + 1)
              / Return.seq (Return.win (fun _ => 0)) m := rfl
      rw [hL, hR, e0, e1, e2, e3]

/-- the 2-adic bound at the centre window: `v₂(a n) ≥ 0` for all `n`. -/
lemma val_nonneg_a (n : ℕ) : 0 ≤ padicValRat 2 (A276175.a n) := by
  rw [a_eq_seq n]
  exact Return.val_nonneg n (fun _ => 0) (fun _ => Return.Int2.zero)

/-- every term of OEIS A276175 is an integer. -/
theorem A276175_integrality (n : ℕ) : ∃ z : ℤ, A276175.a n = z :=
  A276175.integrality val_nonneg_a n
