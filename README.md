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
* **The prime 2.** Over the tube `1 + 16·ℤ₂`, writing `A(n) = 2^{w(n)}·U(n)`
  with `U(n)` a unit turns the recurrence into a unit recurrence with explicit
  `44`-periodic words `w`, `t`. A finite computation in `ℤ₂[[z₀,…,z₃]]`
  (coefficients mod `2^m`) verifies over one period that the valuation follows
  the nonnegative word `w` and that the window returns to `1 + 16·ℤ₂` after
  `44` steps, so it iterates. This finite check is decided by `native_decide`.

This realizes, fully explicitly, the strategy of mercio's answer to the
question above: the cluster embedding `a(n) = x(n+1)x(n+2)x(n+3)` into a
period-one cluster recurrence, together with a `2`-adic neighbourhood of
`(1,1,1,1)` that the recurrence returns to.

## Contents

* [Proof.lean](Proof.lean) — the complete, self-contained Lean 4 / Mathlib
  formalization (~1800 lines). Final statement:

  ```lean
  theorem A276175_integrality (n : ℕ) : ∃ z : ℤ, A276175Cluster.a n = z
  ```

  where `A276175Cluster.a` is defined by nothing but the recurrence above. No
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
