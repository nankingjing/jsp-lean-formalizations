-- Probe 01 — does core Lean 4 (import Init only, NO Mathlib) give us the basic
-- Nat arithmetic simplifications and `decide`?
import Init

example (n : Nat) : n + 0 = n := by simp
example (n : Nat) : n * 1 = n := by simp
example (n : Nat) : 0 + n = n := by simp
example (n : Nat) : n ^ 2 = n * n := by simp [Nat.pow_succ]

example : (2 : Nat) + 2 = 4 := by decide
example : (23 : Nat) * 23 * 23 = 12167 := by decide
example : (2 : Nat) ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by decide

#eval (23 : Nat) * 23 * 23
#eval (2 : Nat) ^ 3 * 3 ^ 2 * 13 ^ 2

#print axioms Nat.add_zero

theorem probe01_add_zero (n : Nat) : n + 0 = n := by simp
#print axioms probe01_add_zero
