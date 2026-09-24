import Init
set_option maxRecDepth 100000

/-!  Round 4, probe 1: inventory of what core Lean 4 actually provides, for the
    graph-theoretic (JSP-000465) and sequence (JSP-000288) targets.

`#check` never fails elaboration of the rest of the file, so a missing name is
reported as an error but everything else still goes through.  The `example`s are
the parts that can actually fail. -/

-- ============================================================================
-- Lists: the only container core Lean 4 has.
-- ============================================================================

#check @List.range
#check @List.range'
#check @List.finRange
#check @List.iota
#check @List.product
#check @List.zip
#check @List.zipWith
#check @List.filter
#check @List.filterMap
#check @List.countP
#check @List.count
#check @List.length
#check @List.erase
#check @List.dedup
#check @List.subset
#check @List.Sublist
#check @List.Perm
#check @List.attach
#check @List.bind
#check @List.join
#check @List.map
#check @List.foldl
#check @List.all
#check @List.any
#check @List.all_eq_true
#check @List.any_eq_true
#check @List.mem_range
#check @List.mem_cons
#check @List.elem

-- ============================================================================
-- Fin: do we get a decidable universal quantifier over `Fin n`?
-- ============================================================================

#check @Fin
#check @Fin.val
#check @Fin.isLt
#check @Fin.mk
#check @instDecidableEqFin
#check @Fin.decidableEq

-- These are the load-bearing questions.  If `inferInstance` fails here, every
-- `∀ v : Fin n, ...` in a graph-theory formalization has to be re-expressed as a
-- `List` scan, because there is no `Fintype` in core to drive `decide`.
example : DecidableEq (Fin 3) := inferInstance
example : Decidable (∀ x : Fin 3, x.val < 3) := inferInstance

-- ============================================================================
-- Finset / Fintype / Mathlib things: expected to be absent.
-- ============================================================================

#check @Finset
#check @Fintype
#check @Multiset
#check @Nat.Prime
#check @Nat.find
#check @Nat.minFac
#check @Nat.dvd_pow
#check @Nat.sqrt_eq
#check @Nat.lt_of_dvd_of_lt

-- ============================================================================
-- Combinatorics-adjacent arithmetic that does survive into core.
-- ============================================================================

#check @Nat.choose
#check @Nat.gcd
#check @Nat.lcm
#check @Nat.factorial
#check @Nat.pow
#check @Nat.log2
#check @Nat.size
#check @Nat.bit0
#check @Nat.decLt
#check @Nat.decLe
#check @Nat.decEq

-- ============================================================================
-- Rat / Int, for the JSP-000288 convergence target.
-- ============================================================================

#check @Rat
#check @Rat.mk
#check @Rat.div
#check @Rat.inv
#check @Rat.num
#check @Rat.den
#check @Rat.le
#check @Rat.lt
#check @Rat.abs
#check @abs
#check @Int
#check @Int.natAbs
#check @Int.ofNat
#check @Int.ediv
#check @Int.fdiv

-- Convergence would need an epsilon-N statement over `Rat`.  These are the
-- pieces `Mathlib` would supply and core will not:
#check @Filter
#check @Filter.Tendsto
#check @Real
#check @abs_of_nonneg
#check @Rat.div_le_div_of_le_left
#check @Rat.mul_le_mul
#check @Rat.sub_lt_iff_lt_add

-- ============================================================================
-- A minimal `Rat` sanity test: can we even do elementary ordered-field algebra?
-- ============================================================================

example : (1 : Rat) / 2 + 1 / 2 = 1 := by decide
example : (1 : Rat) / 3 < 1 / 2 := by decide
example : (2 : Rat) / 3 < 1 := by decide

-- ============================================================================
-- Lists of pairs as edges: the encoding I expect to use for JSP-000465.
-- ============================================================================

/-- An undirected graph on `List.range n` as a duplicate-free edge list, each
    edge written with its smaller endpoint first. -/
abbrev EdgeList (n : Nat) := List (Nat × Nat)

def edgeCount (e : EdgeList n) : Nat := e.length

example : edgeCount ([(0, 1), (1, 2)] : EdgeList 3) = 2 := by decide

/-- Does `e` contain the pair `(a, b)`? -/
def hasEdge (e : EdgeList n) (a b : Nat) : Bool :=
  e.any (fun p => (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a))

#eval hasEdge [(0, 1), (1, 2)] 0 1
#eval hasEdge [(0, 1), (1, 2)] 1 0
#eval hasEdge [(0, 1), (1, 2)] 0 2

#check @Bool.and
#check @Bool.or
#check @Bool.not
#check @beq
#check @decide
