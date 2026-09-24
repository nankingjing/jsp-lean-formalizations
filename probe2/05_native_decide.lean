-- Round 2 / 05 — the axiom footprint question, definitively.
-- Round 1 showed `native_decide` leaves a SELF-INVENTED AXIOM in `#print axioms`.
-- That is exactly the "placeholder or unreviewed axiom" that §7 revokes for.
import Init

set_option maxRecDepth 100000

def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun m => !(decide (1 < m && m < p && m ∣ p)))

-- kernel `decide` — expect: no axioms, or only propext
theorem by_decide : isPrimeB 23 = true := by decide
#print axioms by_decide

-- `native_decide` — expect a fabricated axiom name
theorem by_native : isPrimeB 23 = true := by native_decide
#print axioms by_native

-- how does the fabricated axiom get NAMED? (round 1 saw `by_native._native.native_decide.ax_1_1`)
-- and does `simp`/`omega` drag in propext?
theorem by_simp (n : Nat) : n + 0 = n := by simp
#print axioms by_simp

theorem by_omega (a b : Nat) (h : a = b) : a ≤ b := by omega
#print axioms by_omega

-- `decide` on a modest kernel computation — how slow does it get?
def countTo (n : Nat) : Bool := (List.range n).all (fun k => decide (k < n))
theorem big_kernel : countTo 20000 = true := by decide
#print axioms big_kernel
