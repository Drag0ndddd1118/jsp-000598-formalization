# Lean 4 Formalization of JSP-000598

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.34.0-blue.svg)](https://github.com/leanprover/lean4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Verification](https://img.shields.io/badge/Axioms-Standard%20Core%20Only-green.svg)](#axiom-audit)

Constructive, kernel-verified Lean 4 formalization for **JSP-000598** from the [Justin Sun Prize Awards Catalog](https://github.com/TheJustinSunPrize/awards).

---

## Problem Overview

- **Problem ID:** [JSP-000598](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000598)
- **Title:** *Can two distinct central binomial coefficients have exactly the same prime divisors?*
- **Date Proposed:** No later than 1975 (Erdős, Graham, Ruzsa, Straus [EGRS75])
- **Mathematical Area:** Number theory / Binomial coefficients / Numeral representations
- **Current Status:** Solved (Affirmative counterexample: $n = 87$ and $m = 88$)
- **Formalization Author:** Qin Zhao ([@Drag0ndddd1118](https://github.com/Drag0ndddd1118))

---

## Mathematical Background

In their 1975 paper *"On the prime factors of $\binom{2n}{n}$"* (Math. Comp. 29, 1975, pp. 83–92), Erdős, Graham, Ruzsa, and Straus studied the prime factorizations of central binomial coefficients $C(2n, n) = \binom{2n}{n}$. They raised the question of whether two distinct central binomial coefficients can possess the exact same set of prime factors.

### The Kummer Criterion
By Kummer's Theorem (1852), a prime $p$ divides $\binom{2n}{n}$ if and only if adding $n + n$ in base $p$ generates at least one carry. In positional arithmetic, this is equivalent to:
$$\exists \text{ digit } d \text{ of } n \text{ in base } p \text{ such that } 2d \ge p \quad (\text{i.e. } d \ge \lceil p/2 \rceil).$$

### The Counterexample ($n = 87, m = 88$)
An explicit counterexample is given by $n = 87$ and $m = 88$:

1. **Algebraic Relation:**
   $$\binom{176}{88} = \frac{176 \cdot 175}{88 \cdot 88} \binom{174}{87} = \frac{175}{44} \binom{174}{87}$$
   $$44 \cdot \binom{176}{88} = 175 \cdot \binom{174}{87}$$

2. **Prime Divisor Analysis:**
   - $44 = 2^2 \cdot 11$ and $175 = 5^2 \cdot 7$.
   - For all primes $p \notin \{2, 5, 7, 11\}$, $v_p(44) = 0$ and $v_p(175) = 0$, hence $v_p\left(\binom{176}{88}\right) = v_p\left(\binom{174}{87}\right)$.
   - For $p \in \{2, 5, 7, 11\}$, both numbers have strictly positive $p$-adic valuations:
     - $v_2 = 5$ (for 87) and $3$ (for 88)
     - $v_5 = 1$ (for 87) and $3$ (for 88)
     - $v_7 = 1$ (for 87) and $2$ (for 88)
     - $v_{11} = 2$ (for 87) and $1$ (for 88)
   - Therefore, every prime dividing $\binom{174}{87}$ also divides $\binom{176}{88}$ and vice versa.

3. **Kummer Base-$p$ Digits Verification:**
   - For $p > 176$: $2 \times 88 = 176 < p$, so no carry occurs for either $n = 87$ or $m = 88$.
   - For $p \le 176$: all 40 primes match identically, giving exactly **28 shared prime divisors**:
     $$\{2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173\}$$

---

## Main Theorems Formalized

In `JSP_000598.lean`:

- `centralBinom_87_val`: Verifies the exact 52-digit value of $C(174, 87)$ by kernel evaluation (`rfl`).
- `centralBinom_88_val`: Verifies the exact 52-digit value of $C(176, 88)$ by kernel evaluation (`rfl`).
- `ratio_identity`: Verifies $44 \cdot C(176, 88) = 175 \cdot C(174, 87)$ (`rfl`).
- `hasBasePCarry_of_gt`: Proves that for any $p > 2n$, no base-$p$ carry occurs.
- `primesEqualUpTo176_eq_true`: Finite verification of identical carry status for all primes $p \le 176$ (`rfl`).
- `kummer_same_primes`: Unconditional proof that for all primes $p$, $\text{hasBasePCarry}(87, p) = \text{hasBasePCarry}(88, p)$.
- `shared_divisors_count`: Confirms exactly 28 common prime divisors.
- `jsp_000598`: Main affirmative resolution theorem:
  ```lean
  theorem jsp_000598 :
      ∃ n m : Nat, n ≠ m ∧ 0 < n ∧ 0 < m ∧
        ∀ p : Nat, isPrime p = true → (hasBasePCarry n p = hasBasePCarry m p)
  ```

---

## Build and Verification

### Prerequisites
- Lean 4 toolchain: `v4.34.0` (managed via `elan`)

### Instructions

```bash
# Build library
lake build

# Verify axioms
lake env lean --run check_axioms.lean
```

### Axiom Audit

Running `#print axioms JSP000598.jsp_000598`:
```lean
'JSP000598.jsp_000598' depends on axioms: [propext, Quot.sound]
```
- No `sorry`
- No `admit`
- No non-standard or user-defined axioms

---

## License

MIT License. Copyright (c) 2026 Qin Zhao.

## Statement of record — `Challenge.lean`

`Challenge.lean` declares the definitions the problem is phrased with and the proposition
`JSP000598.jsp000598Statement`. It proves nothing, so a reviewer has only to read that one file to judge *what* has
been claimed.

```lean
  ∃ n m : Nat, n ≠ m ∧ 0 < n ∧ 0 < m ∧
        ∀ p : Nat, isPrime p = true → (hasBasePCarry n p = hasBasePCarry m p)
```

## Proof — `Submission.lean`

`Submission.lean` imports `Challenge.lean`, so the proof and the statement refer to the *same*
`JSP000598.jsp000598Statement` constant and cannot drift apart. The top-level result is

```lean
JSP000598.jsp_000598
```

It depends on `Quot.sound`, `propext` only, and the file contains no `sorry`, no `admit` and no `axiom`
declaration. `check.py` type-checks the bridge

```
example : JSP000598.jsp000598Statement := JSP000598.jsp_000598
```

and re-runs the axiom audit.

## Build and check

```sh
lake build
python3 check.py
```

Toolchain: `leanprover/lean4:v4.34.0` (commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`). The development is self-contained:
it uses Lean core only and depends on no external library.
