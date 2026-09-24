-- Round 2 / 02 — WHICH SHAPE of bounded forall is `decide` able to handle,
-- and does the hypothesis ORDER change whether the computation short-circuits?
-- Round 1 failed on `∀ m, 1 < m → m < p → ...` (bound not first).
import Init

set_option maxRecDepth 100000

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∈ List.range p → 1 < m → ¬ (m ∣ p)
instance (p : Nat) : Decidable (IsPrime p) := by unfold IsPrime; infer_instance

-- (A) bound FIRST:  ∀ p, p < n+1 → ...
def shapeA (n : Nat) : Prop := ∀ p : Nat, p < n + 1 → p ∣ n → IsPrime p → p * p ∣ n

-- (B) bound LAST:   ∀ p, p ∣ n → IsPrime p → p * p ∣ n   (unbounded — expect failure)
def shapeB (n : Nat) : Prop := ∀ p : Nat, p ∣ n → IsPrime p → p * p ∣ n

-- (C) range formulation
def shapeC (n : Nat) : Prop := ∀ p : Nat, p ∈ List.range (n + 1) → p ∣ n → IsPrime p → p * p ∣ n

-- (D) pure Bool: the fallback that needs no Prop-level decidability at all
def shapeD (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p =>
    !(decide (p ∣ n)) || !(decide (IsPrime p)) || decide (p * p ∣ n))

example (n : Nat) : Decidable (shapeA n) := by unfold shapeA; infer_instance
example (n : Nat) : Decidable (shapeC n) := by unfold shapeC; infer_instance

-- Timing/behaviour on the real numbers.
example : shapeA 12167 := by decide
example : shapeA 12168 := by decide
example : shapeC 12167 := by decide

#eval shapeD 12167
#eval shapeD 12168
#eval shapeD 12
