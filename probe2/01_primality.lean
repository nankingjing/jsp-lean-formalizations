-- Round 2 / 01 — round 1 proved `Nat.Prime` DOES NOT EXIST in core Lean 4.
-- So we must roll our own, and make it decidable so the kernel (not the compiler)
-- can check it. This file establishes the idiom.
import Init

set_option maxRecDepth 100000

/-- Primality, hand-rolled. `p` is prime iff `p ≥ 2` and no `m` with `1 < m < p`
    divides `p`. Written with the range membership so it is decidable. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∈ List.range p → 1 < m → ¬ (m ∣ p)

/-- Registered GLOBAL instance — `example ... : Decidable (IsPrime p)` is not enough,
    `decide` needs an instance in the typeclass search. -/
instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime
  infer_instance

-- Kernel-checked primality facts.
example : IsPrime 2 := by decide
example : IsPrime 23 := by decide
example : ¬ IsPrime 22 := by decide
example : ¬ IsPrime 1 := by decide
example : ¬ IsPrime 0 := by decide
example : ¬ IsPrime 12167 := by decide        -- 12167 = 23^3, deliberately composite

-- Sanity: agree with intuition on a few
example : IsPrime 13 := by decide
example : ¬ IsPrime 12168 := by decide

#print axioms IsPrime
theorem p23 : IsPrime 23 := by decide
#print axioms p23
