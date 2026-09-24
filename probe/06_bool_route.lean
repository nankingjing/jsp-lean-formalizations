-- Probe 06 — the guaranteed-safe fallback: define the checks as Bool-valued
-- computations over `List.range`, then bridge Bool → Prop.
-- This needs NO fancy decidable instances: everything is structural recursion.
import Init

/-- trial-division primality test, bool-valued -/
def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun m => !(decide (1 < m && m < p && m ∣ p)))

/-- powerful: every prime divisor p of n satisfies p*p ∣ n -/
def isPowerful (n : Nat) : Prop := ∀ p : Nat, Nat.Prime p → p ∣ n → p * p ∣ n

/-- the bool-valued version of "is powerful", using our own isPrimeB -/
def isPowerfulB (n : Nat) : Bool :=
  decide (0 < n) && (List.range (n + 1)).all (fun p =>
    !(isPrimeB p && decide (p ∣ n)) || decide (p * p ∣ n))

/-- square test -/
def isSquareB (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k => decide (n = k * k))

-- These should all evaluate by kernel computation (`native_decide` or `decide`).
example : isPrimeB 23 = true := by decide
example : isPrimeB 22 = false := by decide
example : isSquareB 12167 = false := by decide
example : isSquareB 12168 = false := by decide

-- Timing-relevant: how big can this get before `decide` chokes?
#eval isPowerfulB 12167
#eval isPowerfulB 12168
#eval isSquareB 12167
#eval (List.range 25).all (fun k => decide (k * k ≠ 12167))

#print axioms isPrimeB
