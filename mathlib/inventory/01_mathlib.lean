/-
  Mathlib inventory probe.

  This file is deliberately **not** reachable from the `lake build` target
  (`Probe.lean`): it is a wall of `#check`s, most of which are expected to fail,
  because the whole point is to find out which of the names the contest
  candidates need actually exist.  CI compiles it with `continue-on-error`, and
  the missing names show up in the log as `unknownIdentifier`.

  Read the log top to bottom: a line with no error means the name resolved.
-/
import Mathlib

/-! ## A. Numbers, primes, divisors -/
#check @Nat.Prime
#check @Nat.factorial
#check @Nat.choose
#check @Nat.sqrt
#check @Nat.divisors
#check @Nat.card_divisors
#check @Nat.Prime.dvd_of_dvd_pow
#check @Nat.Prime.dvd_mul
#check @Nat.exists_infinite_primes
#check @Nat.Prime.eq_two_or_odd
#check @Nat.minFac
#check @Nat.find
#check @Nat.Prime.two_le
#check @Nat.prime_def_lt
#check @Nat.exists_prime_and_dvd
#check @Nat.Prime.not_dvd_one

/-! ## B. Modular arithmetic, residues, covering systems -/
#check @ZMod
#check @ZMod.val
#check @Nat.ModEq
#check @Int.ModEq
#check @Nat.Coprime
#check @ZMod.instField
#check @ZMod.instCommRing
#check @Int.emod_nonneg
#check @Nat.card_eq_fintype_card
#check @Nat.card_Icc
#check @Set.ncard
#check @Set.Finite
#check @Set.Infinite
#check @Nat.density        -- does Mathlib have a natural density?

/-! ## C. Finite combinatorics -/
#check @Finset
#check @Fintype
#check @Finset.card
#check @Finset.filter
#check @Finset.powerset
#check @Finset.card_powerset
#check @Fintype.card
#check @Finset.card_bij
#check @Finset.card_le_card
#check @Finset.card_image_of_injective

/-! ## D. Graphs -/
#check @SimpleGraph
#check @SimpleGraph.Clique
#check @SimpleGraph.chromaticNumber
#check @SimpleGraph.IsBipartite
#check @SimpleGraph.extremalNumber
#check @SimpleGraph.Turan.graph
#check @SimpleGraph.erdos_stone_simonovits
#check @SimpleGraph.zarankiewicz
#check @SimpleGraph.MaximalClique
#check @SimpleGraph.IsNClique
#check @SimpleGraph.degree

/-! ## E. Projective geometry — the Alon JSP-000539 construction -/
#check @Projectivization
#check @Projectivization.mk
#check @Projectivization.Collinear
#check @Projectivization.card
#check @Projectivization.Subspace
#check @GaloisField
#check @GaloisField.card
#check @GaloisField.field
#check @ZMod.instField
#check @FiniteField
#check @IsQuadraticResidue
#check @legendreSym
#check @ZMod.quadraticChar

/-- The projective plane `PG(2, q)` as the projectivization of `GF(q)^3`: the
    single most important object type for JSP-000539. -/
#check @Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)

/-! ## F. Geometry in the plane — Blumenthal, empty polygons, ordinary lines -/
#check @EuclideanSpace
#check @EuclideanGeometry
#check @ConvexHull
#check @Wbtw
#check @Sbtw
#check @Collinear
#check @affineIndependent
#check @InnerProductGeometry.angle
#check @EuclideanGeometry.angle
#check @Convex
#check @convexHull
#check @Set.ncard_union

/-! ## G. Asymptotics — for `ex(n,F) = O(n^{4/3})` style targets -/
#check @Asymptotics.IsBigO
#check @Asymptotics.IsLittleO
#check @Asymptotics.IsTheta
#check @Filter.atTop
#check @Filter.Tendsto
#check @Asymptotics.IsBigO.refl

/-! ## H. Order / choice plumbing -/
#check @Finset.max'
#check @Finset.sup
#check @Finset.induction
#check @WellFounded
#check @Nat.strong_induction_on

/-! ## I. Real / rational algebra -/
#check @Rat
#check @Real
#check @abs
#check @Rat.div
#check @irrational_sqrt_two
