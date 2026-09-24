-- Round 2 / 04 — `¬ IsSquare 12167` : how do we prove a Nat is NOT a perfect square
-- in core Lean, cheaply and without `native_decide`?
import Init

set_option maxRecDepth 100000

def IsSquare (n : Nat) : Prop := ∃ k : Nat, n = k * k

-- (A) bounded by the square root, if `Nat.sqrt` exists in core
example : ¬ IsSquare 12167 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hk_le : k ≤ Nat.sqrt 12167 := by
    apply Nat.le_sqrt.mpr
    omega
  sorry

-- (B) brute force over a range that certainly contains k (k^2 = n > 0 → k ≤ n)
def noSquareB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun k => decide (n ≠ k * k))

#eval noSquareB 12167
#eval noSquareB 12168
#eval noSquareB 12100   -- 110^2, must be false
#eval noSquareB 12169

-- (C) the bridge: if the search says none, prove the Prop
example (n : Nat) (h : noSquareB n = true) : ¬ IsSquare n := by
  intro hs
  obtain ⟨k, hk⟩ := hs
  have hmem : k ∈ List.range (n + 1) := by
    simp [List.mem_range]
    omega
  have := (List.all_eq_true.mp h) k hmem
  simp at this
  omega

theorem notSquare12167 : ¬ IsSquare 12167 := by
  apply (show ∀ n, noSquareB n = true → ¬ IsSquare n from fun n h => by
    intro hs
    obtain ⟨k, hk⟩ := hs
    have hmem : k ∈ List.range (n + 1) := by simp [List.mem_range]; omega
    have := (List.all_eq_true.mp h) k hmem
    simp at this
    omega) 12167
  decide

#print axioms notSquare12167
