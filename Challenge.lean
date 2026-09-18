/-
  The Justin Sun Prize (孙宇晨奖) — JSP-000598

  **Challenge.lean: the statement of record.**

  This file declares the definitions the problem is phrased with, and the proposition
  `jsp000598Statement`. It proves nothing. `Submission.lean` imports this file, so the proof and the
  statement refer to the *same* constant and the statement cannot drift between them.
  `check.py` type-checks the bridge

      example : JSP000598.jsp000598Statement := JSP000598.jsp_000598

  and audits the axioms the submitted proof depends on. A reviewer has only to read this
  file in order to judge *what* has been claimed.
-/


namespace JSP000598

set_option maxRecDepth 2000000

/-! ### Central Binomial Coefficients and Exact Values -/

/-- Standard factorial function. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Central binomial coefficient C(2n, n) = (2n)! / (n! * n!). -/
def centralBinom (n : Nat) : Nat :=
  fact (2 * n) / (fact n * fact n)

/-! ### Kummer Carry Criterion in Base p -/

/-- Computable primality test on natural numbers. -/
def isPrime (p : Nat) : Bool :=
  2 ≤ p && (List.range (p - 2)).all (fun i => p % (i + 2) != 0)

/-- By Kummer's theorem, a prime p divides C(2n, n) iff there is a carry in base p.
    This tail-recursive loop checks if any base-p digit d of m satisfies 2 * d ≥ p. -/
def hasBasePCarryLoop (p : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | m, fuel + 1 =>
    if m = 0 then false
    else if 2 * (m % p) ≥ p then true
    else hasBasePCarryLoop p (m / p) fuel

/-- Kummer base-p carry predicate for C(2n, n). -/
def hasBasePCarry (n p : Nat) : Bool :=
  if p < 2 then false
  else hasBasePCarryLoop p n (n + 1)

/-- For all primes p ≤ 176, the carry status for n = 87 and m = 88 is identical. -/
def primesEqualUpTo176 : Bool :=
  (List.range 177).all (fun p => !isPrime p || (hasBasePCarry 87 p == hasBasePCarry 88 p))

/-! ### Explicit Shared Prime Divisors -/

/-- The exact set of 28 shared prime divisors of C(174, 87) and C(176, 88). -/
def sharedPrimeDivisors : List Nat :=
  [2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173]

/-- **Statement of record for JSP-000598.**

The proposition this development resolves, phrased with the definitions above and
nothing else. -/

def jsp000598Statement : Prop :=
  ∃ n m : Nat, n ≠ m ∧ 0 < n ∧ 0 < m ∧
        ∀ p : Nat, isPrime p = true → (hasBasePCarry n p = hasBasePCarry m p)

end JSP000598
