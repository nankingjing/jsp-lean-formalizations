-- Probe 03 — THE CRUX. Is a bounded-universal over Nat automatically decidable
-- in core Lean 4, so that `decide` can close a hand-rolled primality predicate?
import Init

def IsPrimeH (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, 1 < m → m < p → ¬ (m ∣ p)

-- (a) Can the kernel find a Decidable instance for the bounded forall?
example (p : Nat) : Decidable (IsPrimeH p) := by
  unfold IsPrimeH
  infer_instance

-- (b) If (a) works, does `decide` actually close it?
example : IsPrimeH 23 := by decide

-- (c) Explicit-range formulation, which is the safe fallback.
def IsPrimeR (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∈ List.range p → 1 < m → ¬ (m ∣ p)

example (p : Nat) : Decidable (IsPrimeR p) := by
  unfold IsPrimeR
  infer_instance

example : IsPrimeR 23 := by decide
example : ¬ IsPrimeR 22 := by decide
