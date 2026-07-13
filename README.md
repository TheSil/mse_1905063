# A276175 is integer-only

A proof of the conjecture from
[this Math.StackExchange question](https://math.stackexchange.com/questions/1905063)
(= [OEIS A276175](https://oeis.org/A276175), B. Langlois, 2016): the sequence

```
a(0) = a(1) = a(2) = a(3) = 1
a(n) = (a(n-1) + 1)(a(n-2) + 1)(a(n-3) + 1) / a(n-4)
```

consists only of integers.

The proof shows that `a(n)` has nonnegative `p`-adic valuation at every prime
`p`; the cases of odd `p` and of `p = 2` are handled by different methods.

* **Odd primes.** With `b(n) = a(n) + 1` and the identity
  `b(n+4)·a(n) = a(n) + b(n+1)b(n+2)b(n+3)`, a short valuation induction shows
  divisibility is confined to isolated bursts of terms, giving `a(n) ∈ ℤ[1/2]`.
* **The prime 2.** For rational points of the tube `1 + 16·ℤ₂`,
  explicit `44`-periodic words `w`, `t` govern the normalized recurrence. A
  finite computation with polynomial jets verifies one block, and the proved
  invariant `Rep` connects that computation to the actual rational sequence.
  After `44` steps the window returns to the tube, so the bound iterates. The
  finite check is decided by `native_decide`.

The formal dependency chain is the odd-prime valuation induction, the rational
`2`-adic return argument, and the valuation criterion for rational integers.

## Contents

* [Proof.lean](Proof.lean) — the complete, self-contained Lean 4 / Mathlib
  formalization. Final statement:

  ```lean
  theorem A276175_integrality (n : ℕ) : ∃ z : ℤ, A276175.a n = z
  ```

  where `A276175.a` is defined by nothing but the recurrence above. No
  `sorry`. Depends on the three standard axioms
  `[propext, Classical.choice, Quot.sound]` together with the `native_decide`
  reduction axiom (`Lean.ofReduceBool`), which discharges the finite `2`-adic
  computation.
* [proof.pdf](proof.pdf) ([proof.tex](proof.tex)) — the mathematical
  exposition of the proof.

## Verify

```
lake exe cache get
lake build
```

Builds in a few minutes; every step is checked by the Lean kernel.
