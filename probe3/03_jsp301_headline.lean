import Init
set_option maxRecDepth 100000

/-!  Round 3, probe 3: JSP-000301 end to end, self-contained.

    "If two consecutive positive integers are powerful, must at least one be a
     perfect square?"

    Answer: no.  12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2 are both powerful,
    they are consecutive, and neither is a perfect square.

This file states the conjecture as a `Prop` over `Nat`, refutes it, and prints
the axiom footprint of every headline theorem.  It uses only core Lean 4 — no
Mathlib — and no `native_decide` anywhere. -/

-- ============================================================================
-- Definitions.
-- ============================================================================

/-- Primality.  Core Lean 4 has no `Nat.Prime`, so we roll our own.  Note this
    is the honest unbounded statement ("no divisor strictly between 1 and p"). -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∈ List.range p → 1 < m → ¬ (m ∣ p)

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime
  infer_instance

/-- `n` is powerful iff every prime dividing `n` has its square dividing `n`.
    Honest unbounded form. -/
def IsPowerful (n : Nat) : Prop := ∀ p : Nat, p ∣ n → IsPrime p → p * p ∣ n

/-- `n` is a perfect square. -/
def IsSquare (n : Nat) : Prop := ∃ k : Nat, n = k * k

-- ============================================================================
-- Computable engines.  These are what actually gets evaluated; the theorems
-- below convert their `true` into statements about the honest definitions
-- above, so nothing is proved about a watered-down predicate.
-- ============================================================================

def powerfulB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p => decide (¬ (p ∣ n) ∨ ¬ IsPrime p ∨ p * p ∣ n))

def noSquareB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun k => decide (n ≠ k * k))

-- ============================================================================
-- Bridge 1: the square engine is sound.
-- The content is `Nat.le_mul_self`: a square root of `n` is at most `n`, so the
-- scanned range is exhaustive.
-- ============================================================================

theorem not_isSquare_of_noSquareB (n : Nat) (h : noSquareB n = true) : ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hk_le : k ≤ n := by
    have h1 : k ≤ k * k := Nat.le_mul_self k
    omega
  have hmem : k ∈ List.range (n + 1) := by
    rw [List.mem_range]
    omega
  have hk' := (List.all_eq_true.mp h) k hmem
  simp only [decide_eq_true_eq] at hk'
  exact hk' hk

-- ============================================================================
-- Bridge 2: the powerfulness engine is sound.
-- The content is `Nat.le_of_dvd`: a divisor of a positive `n` is at most `n`.
-- ============================================================================

theorem isPowerful_of_powerfulB (n : Nat) (hn : 0 < n) (h : powerfulB n = true) :
    IsPowerful n := by
  intro p hpn hpr
  have hp_le : p ≤ n := Nat.le_of_dvd hn hpn
  have hmem : p ∈ List.range (n + 1) := by
    rw [List.mem_range]; omega
  have h' := (List.all_eq_true.mp h) p hmem
  simp only [decide_eq_true_eq] at h'
  rcases h' with hnp | hnp | hpp
  · exact absurd hpn hnp
  · exact absurd hpr hnp
  · exact hpp

#print axioms not_isSquare_of_noSquareB
#print axioms isPowerful_of_powerfulB

-- ============================================================================
-- The headline facts.
-- ============================================================================

theorem powerful_12167 : IsPowerful 12167 := isPowerful_of_powerfulB 12167 (by decide) (by decide)
theorem powerful_12168 : IsPowerful 12168 := isPowerful_of_powerfulB 12168 (by decide) (by decide)
theorem notSquare_12167 : ¬ IsSquare 12167 := not_isSquare_of_noSquareB 12167 (by decide)
theorem notSquare_12168 : ¬ IsSquare 12168 := not_isSquare_of_noSquareB 12168 (by decide)

#print axioms powerful_12167
#print axioms powerful_12168
#print axioms notSquare_12167
#print axioms notSquare_12168

/-- The raw evaluation, for the record. -/
#eval powerfulB 12167     -- true
#eval powerfulB 12168     -- true
#eval noSquareB 12167     -- true
#eval noSquareB 12168     -- true
#eval 12167 + 1           -- 12168

/-- The conjunction, in the exact shape the problem asks for: two *consecutive*
    powerful integers, neither of which is a square.  The `12167 + 1 = 12168`
    step is `rfl`, so "consecutive" is not smuggled in. -/
theorem jsp301_witness :
    IsPowerful 12167 ∧ IsPowerful (12167 + 1) ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare (12167 + 1) :=
  ⟨powerful_12167, powerful_12168, notSquare_12167, notSquare_12168⟩

#print axioms jsp301_witness

-- ============================================================================
-- The refutation.  This is the theorem that answers the question: the
-- universally quantified conjecture is false.
-- ============================================================================

/-- The conjecture as posed: any two consecutive *positive* powerful integers
    have at least one perfect square. -/
def Conjecture : Prop :=
  ∀ n : Nat, 0 < n → IsPowerful n → IsPowerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)

theorem jsp301_refutes_conjecture : ¬ Conjecture := by
  intro h
  rcases h 12167 (by decide) powerful_12167 powerful_12168 with hs | hs
  · exact notSquare_12167 hs
  · exact notSquare_12168 hs

#print axioms jsp301_refutes_conjecture

-- ============================================================================
-- Control: the whole thing decided in one kernel term, with no bridging at all,
-- to show the `decide` route is not merely decorative.
-- ============================================================================

theorem jsp301_bool_control :
    (powerfulB 12167 && powerfulB 12168 && noSquareB 12167 && noSquareB 12168) = true := by
  decide

#print axioms jsp301_bool_control
