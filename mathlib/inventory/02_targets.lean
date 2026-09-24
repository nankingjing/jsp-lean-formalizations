/-
  Inventory probe #2 — the names the *front-runner targets* need.

  NOT reachable from the `jsp` build target; compiled tolerantly by CI, where
  every `unknownIdentifier` / `unknownConstant` error is one datum about what
  Mathlib at the pinned revision does and does not supply.

  Front-runners, with the mathematics they need:

  * JSP-000539 (Erdős 664) and JSP-000600 (Erdős 732) — Alon, "Blocking partial
    designs and block-compatible sequences".  Both are finite constructions over
    PG(2, q): count points/lines, use collinearity, and instantiate q as a prime
    power.  So the load-bearing names are the `Projectivization` API, the Galois
    field API, and quadratic-residue machinery.

  * JSP-000598 / JSP-000817 / JSP-000490 — finite colouring and combinatorics,
    needing `Finset`/`Fintype` counting and `Nat.choose`.

  * Every extremal statement is an asymptotic, so the `=O[atTop]` API has to be
    usable with `ℝ`-valued counting functions of `ℕ`.

  Convention below: `#check` (not `#check @`) unless the implicit arguments are
  the point, in which case both are given.  The two are reported separately so a
  failure distinguishes "no such name" from "wrong signature".
-/

import Mathlib

section ProjectiveGeometry
-- Target: JSP-000539, JSP-000600.  PG(2, q): the points and lines of the
-- projective plane over a finite field, and the incidence between them.

#check Projectivization
#check @Projectivization
#check Projectivization.mk
#check Projectivization.mk_eq_mk_iff
#check Projectivization.mk'          -- `Point`/`mk'` spelling varies by revision
#check Projectivization.Point
#check Projectivization.card          -- the load-bearing point count for PG(2, q)
#check @Projectivization.card
#check Projectivization.Collinear
#check Projectivization.Collinear.mk
#check Projectivization.Subspace
#check Projectivization.Subspace.mk
#check Projectivization.independent
#check Projectivization.Independent

-- Can we actually build PG(2, q)?  If these type ascribe, the whole
-- construction is in scope; if they error, we need a bespoke development.
#check Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)
#check Projectivization (ZMod 7) (Fin 3 → ZMod 7)
#check Projectivization.card (k := GaloisField 2 1) (V := Fin 3 → GaloisField 2 1)

-- Anything already packaged as a finite-projective-plane / design?
#check Projectivization.Subspace.card
#check Projectivization.PSL
#check Projectivization.Action
end ProjectiveGeometry

section GaloisFieldsAndResidues
-- Target: the "q a prime power" instantiation, and quadratic-residue
-- constructions (Paley-type graphs, the q ≡ 3 mod 4 cases).

#check GaloisField
#check @GaloisField
#check GaloisField.card
#check GaloisField.instField
#check GaloisField.instFintype
#check GaloisField.instAlgebra
#check GaloisField.exists_prime_pow
#check FiniteField
#check FiniteField.card

#check IsQuadraticResidue
#check legendreSym
#check ZMod.quadraticChar
#check ZMod.exists_sq_eq_neg_one_iff
#check Nat.Prime.eq_two_or_odd
end GaloisFieldsAndResidues

section ExtremalGraphs
-- Target: JSP-000539/600's host object is a hypergraph/design; JSP-000817 and
-- the Kővári–Sós–Turán rows want `ex(n, F)`.

#check SimpleGraph
#check SimpleGraph.Clique
#check SimpleGraph.CliqueFree
#check SimpleGraph.chromaticNumber
#check SimpleGraph.IsBipartite
#check SimpleGraph.IsTriangleFree
#check SimpleGraph.extremalNumber
#check SimpleGraph.Turan.graph
#check SimpleGraph.erdos_stone_simonovits
#check SimpleGraph.zarankiewicz
#check SimpleGraph.Regularity
#check Set.ncard
#check Set.Finite
#check Set.Infinite
#check Set.Finite.toFinset
#check Set.ncard_eq_toFinset_card
end ExtremalGraphs

section FiniteCombinatorics
-- The workhorse layer: everything finite is a `Finset` or a `Fintype`.

#check Fintype.card
#check Fintype.card_congr
#check Finset.card_bij
#check Finset.card_le_card
#check Finset.card_powerset
#check Sym
#check Sym.card
#check Sym.natCard
#check DoubleCounting
#check Finset.max'
#check Finset.sup
#check Nat.choose
#check Nat.descFactorial
#check Nat.factorial
#check Nat.divisors
#check Nat.ModEq
#check Nat.Coprime
#check Nat.Prime
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.exists_infinite_primes
#check Nat.find
#check Nat.minFac
#check Nat.sqrt
#check Nat.density
end FiniteCombinatorics

section Asymptotics
-- Every extremal bound is an asymptotic.  NOTE the codomain must be a normed
-- group: `ℕ` has no `Norm` instance, so counting functions have to be coerced
-- to `ℝ` before `=O[atTop]` typechecks (this bit us in `Probe.lean`).

#check Asymptotics.IsBigO
#check Asymptotics.IsTheta
#check Asymptotics.IsLittleO
#check Asymptotics.IsOmega
#check Filter.atTop
#check Filter.Tendsto
#check Filter.Eventually
#check Filter.eventually_ge_atTop
#check Asymptotics.isBigO_refl
#check Asymptotics.IsBigO.refl
#check Asymptotics.IsBigO.of_bound
#check Asymptotics.IsBigO.trans
#check Asymptotics.IsBigO.add
#check Asymptotics.IsBigO.const_mul_left
#check Asymptotics.IsBigO.mul
#check Asymptotics.IsBigO.pow
end Asymptotics

section RealAndRational
#check Rat
#check Real
#check irrational_sqrt_two
#check Real.rpow
#check Real.log
#check Real.sqrt_le_sqrt
#check Nat.cast_le
end RealAndRational
