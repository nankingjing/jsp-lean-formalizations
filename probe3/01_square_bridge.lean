import Init
set_option maxRecDepth 100000

/-!  Round 3, probe 1: the square bridge that failed in round 2.

Round 2 (`probe2/04_square.lean`) tried to prove

    noSquareB n = true -> ¬ IsSquare n

and got stuck: `omega` was asked for `k ≤ k * k`, which is *nonlinear*, and
`omega` only does linear arithmetic (`omega could not prove the goal: possible
counterexample may satisfy the constraints ... a - b ≤ -1 where a := ↑k * ↑k`).
The fix is to feed it the nonlinear fact `Nat.le_mul_self k : k ≤ k * k` as a
hypothesis, after which everything left is linear in the atoms `k` and `k * k`.
-/

def IsSquare (n : Nat) : Prop := ∃ k : Nat, n = k * k

/-- Scan `0 .. n` and check that no `k` squares to `n`. -/
def noSquareB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun k => decide (n ≠ k * k))

-- ============================================================================
-- Variant A: the intended proof.
-- ============================================================================

theorem not_isSquare_of_noSquareB (n : Nat) (h : noSquareB n = true) : ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  -- `k * k = n` together with `k ≤ k * k` gives `k ≤ n`, i.e. the witness is
  -- inside the range we scanned.  Supplying `Nat.le_mul_self` explicitly is the
  -- whole fix: on its own `omega` cannot find this nonlinear fact.
  have hk_le : k ≤ n := by
    have h1 : k ≤ k * k := Nat.le_mul_self k
    omega
  have hmem : k ∈ List.range (n + 1) := by
    rw [List.mem_range]
    omega
  have hk' := (List.all_eq_true.mp h) k hmem
  simp only [decide_eq_true_eq] at hk'
  exact hk' hk

#print axioms not_isSquare_of_noSquareB

-- ============================================================================
-- Variant B: how we actually want to state it — universally quantified, so the
-- statement is about every `Nat`, not about a single literal.
-- ============================================================================

theorem square_bridge (n : Nat) : noSquareB n = true → ¬ IsSquare n :=
  fun h => not_isSquare_of_noSquareB n h

#print axioms square_bridge

-- ============================================================================
-- Variant C: pin down the `Nat.sqrt` lemmas, in case they are needed later.
-- These are `#check`s only — if a name is missing, the error names it and the
-- rest of this file still elaborates.
-- ============================================================================

#check @Nat.sqrt_le
#check @Nat.lt_succ_sqrt
#check @Nat.mul_le_mul
#check @Nat.le_of_dvd
#check @Nat.pos_of_dvd_of_pos
#check @Nat.le_mul_self
#check @Nat.mul_self_le_mul_self
#check @Nat.pow_dvd_pow
#check @Nat.dvd_of_mod_eq_zero
#check @Nat.mod_eq_zero_of_dvd
#check @List.all_eq_true
#check @decide_eq_true_eq

-- ============================================================================
-- The two numbers in JSP-000301.  12167 = 23^3,  12168 = 8 * 9 * 169.
-- ============================================================================

#eval noSquareB 12167      -- expect true
#eval noSquareB 12168      -- expect true
#eval noSquareB 12100      -- expect false (110^2)
#eval noSquareB 9          -- expect false (3^2)
#eval noSquareB 0          -- expect false (0^2)
#eval noSquareB 1          -- expect false (1^2)
#eval noSquareB 2          -- expect true

theorem ns_12167 : ¬ IsSquare 12167 := not_isSquare_of_noSquareB 12167 (by decide)
theorem ns_12168 : ¬ IsSquare 12168 := not_isSquare_of_noSquareB 12168 (by decide)

#print axioms ns_12167
#print axioms ns_12168

theorem both_ns : ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 := ⟨ns_12167, ns_12168⟩

#print axioms both_ns
