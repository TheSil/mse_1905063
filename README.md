# A276175 is integer-only

A proof of the conjecture from
[this Math.StackExchange question](https://math.stackexchange.com/questions/1905063)
(= [OEIS A276175](https://oeis.org/A276175), B. Langlois, 2016): the sequence

```
a(0) = a(1) = a(2) = a(3) = 1
a(n) = (a(n-1) + 1)(a(n-2) + 1)(a(n-3) + 1) / a(n-4)
```

consists only of integers.

## Contents

* [proof.pdf](proof.pdf) ([proof.tex](proof.tex)) — the mathematical
  exposition of the proof.
  For odd primes, a short valuation induction shows divisibility is confined
  to bursts of three consecutive terms. At the prime 2, the 2-adic valuation
  of `a(n)` follows an explicit word of period 44, proven by a certified
  computation: an induction over 11-step segments of the orbit, with the
  deviation of each period confined to an explicit lattice tube and the
  required 2-adic estimates established by certified polynomial (jet)
  approximations of the segment maps.
* [Proof.lean](Proof.lean) — the complete, self-contained Lean 4 / Mathlib
  formalization (definitions, soundness lemmas, the full certificate, and
  the assembly). Final statement:

  ```lean
  theorem a276175_integrality (n : ℕ) : ∃ z : ℤ, a n = z
  ```

  where `a` is defined by nothing but the recurrence above. No `sorry`;
  depends only on the three standard axioms
  `[propext, Classical.choice, Quot.sound]`.
* [verification.py](verification.py) — independent sanity check by exact
  rational arithmetic for `n ≤ 26`.

## Verify

```
lake exe cache get
lake build
```

Builds in a few minutes (the file is large — most of it is machine-generated
certificate data: orbit residues, tube generators, jets, inversion
witnesses — but every step is checked by the Lean kernel).
