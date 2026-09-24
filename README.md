# jsp-lean-formalizations

Lean 4 formalizations contributed toward **The Justin Sun Prize** (<https://github.com/TheJustinSunPrize/awards>).

This repository is the external proof repository required by §4.1 of the
Selection Rules: Lean source lives here, while the prize catalogue row only
links to it.

## Layout

| Directory | Problem | Status |
| --- | --- | --- |
| `probe/` | toolchain probes (not submissions) | — |
| `jsp301/` | JSP-000301 — consecutive powerful numbers and perfect squares | in progress |
| `jsp465/` | JSP-000465 — forbidden families containing a bipartite graph | in progress |
| `jsp288/` | JSP-000288 — ratios in minimal stably complete sequences | in progress |

Every package targets `leanprover/lean4:v4.34.0` and depends on **core Lean 4
only — no Mathlib**. This keeps the build small and reproducible, and keeps the
axiom footprint minimal, which §7 of the rules audits for.

## Reproduction

```bash
cd jsp301          # or jsp465 / jsp288
lake build
```

CI (`.github/workflows/lean.yml`) installs the pinned toolchain and runs
`lake build` on every push; the build log is the axiom audit, because each
package ends with `#print axioms` for every headline theorem.

## Axioms

The target is `#print axioms` reporting nothing beyond
`propext`, `Classical.choice`, `Quot.sound` — and ideally nothing at all.
Any use of `native_decide` is called out explicitly in the package `AUDIT.md`,
because it trusts the compiler in addition to the kernel.
