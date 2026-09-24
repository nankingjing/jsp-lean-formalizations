-- Probe 05 — is the `omega` tactic available in core Lean 4 with only `import Init`?
import Init

example (a b : Nat) (h : a = b) : a ≤ b := by omega

example (a b : Nat) (h : a < b) : a ≠ b := by omega

example (a : Nat) (h : 12 ≤ a) : 5 ≤ a := by omega

-- linear arithmetic with multiplication by constants
example (a : Nat) (h : a * 3 = 15) : a = 5 := by omega
