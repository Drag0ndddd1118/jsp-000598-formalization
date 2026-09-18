/-
# Formalization of JSP-000598 (Central Binomial Coefficients with Identical Prime Divisors)

*Problem Statement (JSP-000598):*
"Can two distinct central binomial coefficients have exactly the same prime divisors?"

*Mathematical Area:*
Number theory / Binomial coefficients / Numeral representations

*Current Status:*
Solved (Affirmative: n = 87 and m = 88)

*Historical and Mathematical Background:*
In their 1975 paper "On the prime factors of \binom{2n}{n}" (Mathematics of Computation 29, 1975,
pp. 83–92), Paul Erdős, Ronald L. Graham, Imre Z. Ruzsa, and Ernst G. Straus investigated the prime
factors of the central binomial coefficients C(2n, n). A celebrated open question was whether two
distinct central binomial coefficients C(2n, n) and C(2m, m) can ever have the exact same set
of prime divisors.

By Kummer's Theorem (1852), a prime p divides the binomial coefficient C(2n, n) if and only if
there is at least one carry when adding n + n in base p. In positional arithmetic, adding n + n
produces a carry in base p if and only if at least one base-p digit d of n satisfies 2 * d ≥ p
(i.e. d ≥ ⌈p / 2⌉).

An affirmative solution is provided by the pair:
  n = 87 and m = 88.

Algebraically, the central binomial coefficients satisfy:
  C(176, 88) = (176 * 175) / (88 * 88) * C(174, 87)
             = (2 * 175) / 88 * C(174, 87)
             = (175 / 44) * C(174, 87).
Hence:
  44 * C(176, 88) = 175 * C(174, 87).

Since 44 = 2^2 * 11 and 175 = 5^2 * 7:
1. For any prime p ∉ {2, 5, 7, 11}, the p-adic valuations satisfy:
     v_p(C(176, 88)) = v_p(C(174, 87)).
2. For p ∈ {2, 5, 7, 11}, both C(174, 87) and C(176, 88) are divisible by p:
   - p = 2:  v_2(C(174, 87)) = 5, v_2(C(176, 88)) = 3.
   - p = 5:  v_5(C(174, 87)) = 1, v_5(C(176, 88)) = 3.
   - p = 7:  v_7(C(174, 87)) = 1, v_7(C(176, 88)) = 2.
   - p = 11: v_11(C(174, 87)) = 2, v_11(C(176, 88)) = 1.

Therefore, for ALL prime numbers p:
  p ∣ C(174, 87) ↔ p ∣ C(176, 88).

Furthermore, by Kummer's digit criterion:
- For p > 176: 2 * 87 = 174 < p and 2 * 88 = 176 < p, so no carry occurs for either number.
- For p ≤ 176: the carry status matches for all 40 primes up to 176, yielding exactly 28 common
  prime divisors: {2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109, 113,
  127, 131, 137, 139, 149, 151, 157, 163, 167, 173}.

*Axiom Status:*
Clean. Zero custom axioms, zero sorry, kernel-verified in Lean 4 core ([propext, Quot.sound]).
-/

import Challenge

namespace JSP000598

set_option maxRecDepth 2000000

/-- C(174, 87) evaluated in Lean 4 kernel (52 digits). -/
theorem centralBinom_87_val :
    centralBinom 87 = 1446307705450557558142084756547133980616347954754720 := by
  rfl

/-- C(176, 88) evaluated in Lean 4 kernel (52 digits). -/
theorem centralBinom_88_val :
    centralBinom 88 = 5752360192132899378974200736267010150178656638229000 := by
  rfl

/-- Fundamental algebraic relation between C(176, 88) and C(174, 87):
    44 * C(176, 88) = 175 * C(174, 87). -/
theorem ratio_identity :
    44 * centralBinom 88 = 175 * centralBinom 87 := by
  rfl

theorem hasBasePCarry_zero (p : Nat) (fuel : Nat) : hasBasePCarryLoop p 0 fuel = false := by
  cases fuel <;> rfl

/-- For any prime p > 2 * n, 2 * n < p, so the only base-p digit of n is n itself,
    and 2 * n < p ensures no carry occurs. -/
theorem hasBasePCarry_of_gt {n p : Nat} (hp : 2 ≤ p) (h : 2 * n < p) :
    hasBasePCarry n p = false := by
  unfold hasBasePCarry
  split
  · next hlt => omega
  · next hge =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      unfold hasBasePCarryLoop
      split
      · next heq => omega
      · next hne =>
        split
        · next hge2 =>
          have hmod : (n + 1) % p = n + 1 := Nat.mod_eq_of_lt (by omega)
          omega
        · next hlt2 =>
          have hdiv : (n + 1) / p = 0 := Nat.div_eq_of_lt (by omega)
          rw [hdiv]
          exact hasBasePCarry_zero p (n + 1)

theorem primesEqualUpTo176_eq_true : primesEqualUpTo176 = true := by
  rfl

theorem all_range_get {f : Nat → Bool} {n : Nat} (h : (List.range n).all f = true)
    {p : Nat} (hp : p < n) : f p = true := by
  have hmem : p ∈ List.range n := List.mem_range.2 hp
  exact List.all_eq_true.1 h p hmem

/-- For every prime p, Kummer carry occurs for 87 if and only if it occurs for 88. -/
theorem kummer_same_primes (p : Nat) (hp : isPrime p = true) :
    hasBasePCarry 87 p = hasBasePCarry 88 p := by
  by_cases hle : p < 177
  · have hf := all_range_get primesEqualUpTo176_eq_true hle
    change (!isPrime p || (hasBasePCarry 87 p == hasBasePCarry 88 p)) = true at hf
    rw [hp] at hf
    revert hf
    cases hasBasePCarry 87 p <;> cases hasBasePCarry 88 p <;> decide
  · have hp2 : 2 ≤ p := by omega
    have h87 : hasBasePCarry 87 p = false := hasBasePCarry_of_gt hp2 (by omega)
    have h88 : hasBasePCarry 88 p = false := hasBasePCarry_of_gt hp2 (by omega)
    rw [h87, h88]

/-- Exactly 28 primes divide both central binomial coefficients. -/
theorem shared_divisors_count : sharedPrimeDivisors.length = 28 := by
  rfl

/-- Every prime in the shared list has carry for n = 87. -/
theorem shared_divisors_87 :
    sharedPrimeDivisors.all (fun p => hasBasePCarry 87 p) = true := by
  rfl

/-- Every prime in the shared list has carry for m = 88. -/
theorem shared_divisors_88 :
    sharedPrimeDivisors.all (fun p => hasBasePCarry 88 p) = true := by
  rfl

/-! ### Main Theorem -/

/-- Main theorem: affirmative answer to JSP-000598.
    There exist distinct positive integers n and m (explicitly n = 87, m = 88) whose
    central binomial coefficients have exactly the same prime divisors. -/
theorem jsp_000598 :
    ∃ n m : Nat, n ≠ m ∧ 0 < n ∧ 0 < m ∧
      ∀ p : Nat, isPrime p = true → (hasBasePCarry n p = hasBasePCarry m p) := by
  exact ⟨87, 88, by decide, by decide, by decide, kummer_same_primes⟩

end JSP000598

#print axioms JSP000598.jsp_000598
