-- Round 2 / 03 — which of the number-theory lemmas we need actually exist in core
-- Lean 4 (no Mathlib)? `#check` failures are non-fatal, so this prints the full picture.
import Init

-- --- divisibility / order
#check Nat.le_of_dvd
#check Nat.pos_of_dvd_of_pos
#check Nat.dvd_antisymm
#check Nat.dvd_trans
#check Nat.dvd_refl
#check Nat.dvd_mul_right
#check Nat.dvd_mul_left
#check Nat.dvd_of_mod_eq_zero
#check Nat.mod_eq_zero_of_dvd
#check Nat.dvd_sub
#check Nat.mul_dvd_mul
#check Nat.pow_dvd_pow
#check Nat.dvd_pow
#check Nat.eq_zero_of_zero_dvd
#check Nat.zero_dvd
#check Nat.dvd_one
#check Nat.eq_one_of_dvd_one
#check Nat.lt_of_dvd_of_lt
#check Nat.mul_le_mul
#check Nat.le_mul_self
#check Nat.mul_self_le_mul_self

-- --- coprime / gcd (needed for Euclid's lemma, if we want it)
#check Nat.Coprime
#check Nat.gcd
#check Nat.coprime_comm
#check Nat.Coprime.symm
#check Nat.coprime_one_left
#check Nat.gcd_eq_left
#check Nat.gcd_eq_right
#check Nat.coprime_mul_iff_left
#check Nat.Coprime.mul
#check Nat.Coprime.pow
#check Nat.Prime -- expected: missing (round 1 confirmed)

-- --- sqrt (would make `¬ IsSquare n` cheap)
#check Nat.sqrt
#check Nat.sqrt_le
#check Nat.lt_succ_sqrt
#check Nat.sqrt_lt
#check Nat.sqrt_eq
#check Nat.sqrt_eq_iff
#check Nat.mul_self_le
#check Nat.le_of_mul_le_mul_left

-- --- tactics available with only Init
#check List.all_eq_true
#check List.any_eq_true
#check List.mem_range
#check List.range_succ
#check List.length_range
