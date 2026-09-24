-- Probe 07 — does `native_decide` work in core Lean 4, and what does `#print axioms`
-- report for a theorem closed by `native_decide` vs by `decide`?
-- This matters: the JSP verifier flags `native_decide` separately as extra trust.
import Init

def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun m => !(decide (1 < m && m < p && m ∣ p)))

theorem probe_decide : isPrimeB 23 = true := by decide
theorem probe_native : isPrimeB 12167 = true := by native_decide

#print axioms probe_decide
#print axioms probe_native

-- What is the biggest computation native_decide will still do in CI?
def bigCheck (n : Nat) : Bool := (List.range n).all (fun k => decide (k * k ≠ 12167))
theorem probe_big : bigCheck 112 = true := by native_decide
#print axioms probe_big
