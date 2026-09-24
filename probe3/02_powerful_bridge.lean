import Init
set_option maxRecDepth 100000

/-!  Round 3, probe 2: `IsPowerful` in the honest (unbounded) form, plus a
computable Boolean check and a *proved* bridge between them.

The mathematical definition is unbounded — "every prime `p` dividing `n` has
`p * p ∣ n`" — because that is what the original problem statement means.  A
bounded variant is only used as the computational engine, and the bridge theorem
below converts a `true` from the engine into the honest statement, so there is no
gap between the thing we compute and the thing we claim. -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∈ List.range p → 1 < m → ¬ (m ∣ p)

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime
  infer_instance

/-- The honest, unbounded definition: every prime dividing `n` has its square
    dividing `n`.  This is the statement about `Nat` — no ranges, no scanning. -/
def IsPowerful (n : Nat) : Prop := ∀ p : Nat, p ∣ n → IsPrime p → p * p ∣ n

/-- The complementary form, which `decide` can see through because it is a
    disjunction of decidable propositions. -/
def IsPowerfulD (n : Nat) : Prop :=
  ∀ p : Nat, p ∈ List.range (n + 1) → ¬ (p ∣ n) ∨ ¬ IsPrime p ∨ p * p ∣ n

/-- The Boolean engine that actually gets evaluated. -/
def powerfulB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p => decide (¬ (p ∣ n) ∨ ¬ IsPrime p ∨ p * p ∣ n))

-- ============================================================================
-- Bridge: Boolean engine ⟹ bounded Prop form.
-- ============================================================================

theorem isPowerfulD_of_powerfulB (n : Nat) (h : powerfulB n = true) : IsPowerfulD n := by
  intro p hp
  have h' := (List.all_eq_true.mp h) p hp
  simpa only [decide_eq_true_eq] using h'

#print axioms isPowerfulD_of_powerfulB

-- ============================================================================
-- Bridge: bounded Prop form ⟹ honest unbounded form.
-- The only mathematical input is `Nat.le_of_dvd`: a divisor of a positive `n`
-- is at most `n`.  This is what makes the bounded scan exhaustive.
-- ============================================================================

theorem isPowerful_of_isPowerfulD (n : Nat) (hn : 0 < n) (h : IsPowerfulD n) :
    IsPowerful n := by
  intro p hpn hpr
  have hp_le : p ≤ n := Nat.le_of_dvd hn hpn
  have hmem : p ∈ List.range (n + 1) := by
    rw [List.mem_range]; omega
  rcases h p hmem with hnp | hnp | hpp
  · exact absurd hpn hnp
  · exact absurd hpr hnp
  · exact hpp

#print axioms isPowerful_of_isPowerfulD

-- ============================================================================
-- The composite bridge, and the headline facts for JSP-000301.
-- ============================================================================

theorem isPowerful_of_powerfulB (n : Nat) (hn : 0 < n) (h : powerfulB n = true) :
    IsPowerful n :=
  isPowerful_of_isPowerfulD n hn (isPowerfulD_of_powerfulB n h)

#print axioms isPowerful_of_powerfulB

-- `12167 = 23^3`;  `12168 = 2^3 * 3^2 * 13^2 = 8 * 9 * 169`.
-- Primes dividing 12167: 23.   Primes dividing 12168: 2, 3, 13.
#eval powerfulB 12167     -- expect true
#eval powerfulB 12168     -- expect true
#eval powerfulB 12        -- expect false (2 | 12 but 4 ∤ 12)
#eval powerfulB 1         -- expect true
#eval powerfulB 36        -- expect true  (36 = 2^2 * 3^2)
#eval powerfulB 18        -- expect false (3^2 = 9 ∤ 18)

-- Sanity: the engine agrees with the honest definition on the small cases where
-- we can see the answer by hand.
theorem pow_12167 : IsPowerful 12167 := isPowerful_of_powerfulB 12167 (by decide) (by decide)
theorem pow_12168 : IsPowerful 12168 := isPowerful_of_powerfulB 12168 (by decide) (by decide)

/-- `12 = 2^2 * 3`.  The prime `3` divides `12` but `9` does not, so `12` is *not*
    powerful.  (The witness has to be `3`, not `2`: `4` does divide `12`.) -/
theorem not_pow_12 : ¬ IsPowerful 12 := by
  intro h
  have h3 : IsPrime 3 := by decide
  have hd : (3 : Nat) ∣ 12 := by decide
  have h9 : (3 * 3 : Nat) ∣ 12 := h 3 hd h3
  exact absurd h9 (by decide)

-- The same three facts decided directly, as a control on the bridge: if
-- `by decide` can prove them here, the bridge is not doing the work.
theorem not_pow_12' : ¬ IsPowerful 12 := by
  intro h
  exact absurd (h 3 (by decide) (by decide)) (by decide)

#print axioms pow_12167
#print axioms pow_12168
#print axioms not_pow_12
#print axioms not_pow_12'
