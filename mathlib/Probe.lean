/-
  Smoke tests for the Mathlib-based pipeline.

  This file is the `lake build` target.  It must stay *clean*: everything in it
  has to compile, because a green `lake build` is what the prize rules audit.

  The question it answers is narrow but load-bearing: does the pinned toolchain
  plus Mathlib actually build in CI, and do the tactics we intend to lean on
  (`omega`, `norm_num`, `ring`, `positivity`, `decide`, `simp`) work on the kind
  of goal the contest problems produce?
-/
import Mathlib

open Finset

namespace Jsp.Probe

/-! ### Arithmetic tactics on ℕ, ℤ, ℚ, ℝ -/

example (n : ℕ) : n + 0 = n := rfl

example (n : ℕ) (h : 0 < n) : 0 < n * 2 := by omega

example : Nat.Prime 7 := by norm_num

example : Nat.factorial 5 = 120 := by norm_num

example : Nat.choose 10 3 = 120 := by decide

example (n : ℕ) : (n : ℤ) ^ 2 ≥ 0 := by positivity

example : (3 : ℚ) / 2 + 1 / 2 = 2 := by norm_num

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

/-! ### Finset / Fintype: the workhorses for finite combinatorics -/

example : (range 10).card = 10 := by decide

example : ((range 10).filter Nat.Prime).card = 4 := by decide

/-- A finite set of points in the plane, as the extremal-configuration problems
    will need to phrase "no `k` of them are collinear". -/
example : (range 5).card ≤ 5 := by simp

/-! ### Asymptotics: `ex(n, F) = O(n ^ (4/3))` has to be spellable somehow

Note the codomain is `ℝ`, not `ℕ`: `=O[·]` is stated for normed groups and `ℕ`
carries no `Norm` instance, so `(fun n : ℕ => n ^ 2) =O[atTop] (fun n : ℕ => n ^ 2)`
fails instance synthesis.  Every asymptotic statement about `ℕ`-valued counting
functions has to be coerced to `ℝ` first. -/

example : (fun n : ℕ => (n : ℝ) ^ 2) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2) :=
  Asymptotics.isBigO_refl _ _

example : (fun n : ℕ => (n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  simpa using Asymptotics.IsBigO.of_bound 1 (by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (by linarith : (0 : ℝ) ≤ n - 1)])

end Jsp.Probe
