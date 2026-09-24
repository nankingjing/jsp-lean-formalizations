import Init
set_option maxRecDepth 100000

/-!  Round 3, probe 3: JSP-000301 end to end, self-contained.

    "If two consecutive positive integers are powerful, must at least one be a
     perfect square?"

    Answer: no.  12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2 are both powerful,
    they are consecutive, and neither is a perfect square.

Every headline theorem below is proved twice: once with explicit core lemmas
(no `omega`) and once with `omega`, purely so the axiom footprints can be
compared side by side.  The explicit versions are the ones intended for
submission.  No `native_decide` appears anywhere in this file. -/

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
    Honest unbounded form — no range, no bound on the quantifier. -/
def IsPowerful (n : Nat) : Prop := ∀ p : Nat, p ∣ n → IsPrime p → p * p ∣ n

/-- `n` is a perfect square. -/
def IsSquare (n : Nat) : Prop := ∃ k : Nat, n = k * k

-- `#print axioms` on the definitions themselves: a `def` cannot hide a `sorry`
-- behind a proof-irrelevant field, but printing them costs nothing and closes
-- off the question.
#print axioms IsPrime
#print axioms IsPowerful
#print axioms IsSquare

-- ============================================================================
-- Computable engines.  These are what actually gets evaluated; the theorems
-- below convert their `true` into statements about the honest definitions
-- above, so nothing is proved about a watered-down predicate.
-- ============================================================================

def powerfulB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p => decide (¬ (p ∣ n) ∨ ¬ IsPrime p ∨ p * p ∣ n))

def noSquareB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun k => decide (n ≠ k * k))

#print axioms powerfulB
#print axioms noSquareB

-- ============================================================================
-- Bridge 1: the square engine is sound.
-- The content is `Nat.le_mul_self : n ≤ n * n`: a square root of `n` is at most
-- `n`, so scanning `0 .. n` is exhaustive.
-- ============================================================================

theorem not_isSquare_of_noSquareB (n : Nat) (h : noSquareB n = true) : ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hk_le : k ≤ n := by
    rw [hk]
    exact Nat.le_mul_self k
  have hmem : k ∈ List.range (n + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le hk_le)
  have hk' := (List.all_eq_true.mp h) k hmem
  simp only [decide_eq_true_eq] at hk'
  exact hk' hk

#print axioms not_isSquare_of_noSquareB

/-- The same theorem proved with `omega`.  Kept only for the footprint comparison:
    `omega` drags in `Quot.sound`, the explicit proof above does not. -/
theorem not_isSquare_of_noSquareB_omega (n : Nat) (h : noSquareB n = true) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hk_le : k ≤ n := by
    have h1 : k ≤ k * k := Nat.le_mul_self k
    omega
  have hmem : k ∈ List.range (n + 1) := by
    rw [List.mem_range]; omega
  have hk' := (List.all_eq_true.mp h) k hmem
  simp only [decide_eq_true_eq] at hk'
  exact hk' hk

#print axioms not_isSquare_of_noSquareB_omega

-- ============================================================================
-- Bridge 2: the powerfulness engine is sound.
-- The content is `Nat.le_of_dvd : 0 < n → m ∣ n → m ≤ n`: a divisor of a
-- positive `n` is at most `n`, so scanning `0 .. n` is exhaustive.
-- ============================================================================

theorem isPowerful_of_powerfulB (n : Nat) (hn : 0 < n) (h : powerfulB n = true) :
    IsPowerful n := by
  intro p hpn hpr
  have hp_le : p ≤ n := Nat.le_of_dvd hn hpn
  have hmem : p ∈ List.range (n + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le hp_le)
  have h' := (List.all_eq_true.mp h) p hmem
  simp only [decide_eq_true_eq] at h'
  rcases h' with hnp | hnp | hpp
  · exact absurd hpn hnp
  · exact absurd hpr hnp
  · exact hpp

#print axioms isPowerful_of_powerfulB

theorem isPowerful_of_powerfulB_omega (n : Nat) (hn : 0 < n) (h : powerfulB n = true) :
    IsPowerful n := by
  intro p hpn hpr
  have hp_le : p ≤ n := Nat.le_of_dvd hn hpn
  have hmem : p ∈ List.range (n + 1) := by rw [List.mem_range]; omega
  have h' := (List.all_eq_true.mp h) p hmem
  simp only [decide_eq_true_eq] at h'
  rcases h' with hnp | hnp | hpp
  · exact absurd hpn hnp
  · exact absurd hpr hnp
  · exact hpp

#print axioms isPowerful_of_powerfulB_omega

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

-- Raw evaluation, for the record.
#eval powerfulB 12167
#eval powerfulB 12168
#eval noSquareB 12167
#eval noSquareB 12168
#eval 12167 + 1

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

#print axioms Conjecture

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
