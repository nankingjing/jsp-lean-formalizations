-- Probe 02 — is `Nat.Prime` present and decidable in core Lean 4 without Mathlib?
import Init

#check Nat.Prime
#check Nat.prime_def_lt
#check Nat.Prime.two_le
#check Nat.prime_two
#check Nat.Prime.dvd_of_dvd_pow

-- Is there a Decidable instance / a decidable primality test in core?
#check Nat.decidablePrime
#check @instDecidablePrime
#check Nat.minFac
#check Nat.minFac_prime
#check Nat.minFac_le

-- The workhorse Mathlib lemma — almost certainly ABSENT from core:
#check Nat.Prime.dvd_mul
#check Nat.Prime.eq_two_or_odd
#check Nat.exists_prime_and_dvd

-- Can `decide` prove an explicit primality fact using whatever core offers?
example : Nat.Prime 23 := by decide
