# Architecture

This note fixes the module layout before the Lean development grows. The aim
is a library of general, Mathlib-shaped objects (partitions and hooks,
q-analogues, exponent filters, positive traces, Macdonald polynomials) with
the partition-division theorem as a thin top layer. Each general module should
be usable, and upstreamable, without the theorem.

Nothing in this note is a formalization claim. Proof status lives in
`docs/PROOF_OUTLINE.md` and `HANDOFF.md`.

## Layers

```text
PartitionDivision/
  Mathlib/      upstream-shaped lemmas for files Mathlib already has
  TauCeti/      files ported from Tau Ceti, kept at their original paths
  QAnalog/      q-integers, q-factorials, q-binomials, q-Pochhammer symbols
  Macdonald/    Macdonald P polynomials in finitely many variables
  Division/     the partition-division operator and the main theorem
```

Imports only point down this list:

| Layer | May import |
|---|---|
| `Mathlib/` | Mathlib, other `Mathlib/` files |
| `TauCeti/` | Mathlib, `Mathlib/`, other `TauCeti/` files |
| `QAnalog/` | the layers above |
| `Macdonald/` | the layers above, `QAnalog/` |
| `Division/` | everything |

Nothing under `Mathlib/`, `TauCeti/`, `QAnalog/` or `Macdonald/` may mention
partition division. A lemma needed only by the theorem lives in `Division/`.
An import-boundary check in CI will enforce the table once the first general
modules land.

## Naming

- `PartitionDivision/Mathlib/X/Y.lean` targets Mathlib file `Mathlib/X/Y.lean`
  and uses that file's namespaces (`MvPolynomial`, `Matrix`, `Nat.Partition`,
  `YoungDiagram`, `IsPrimitiveRoot`). It never opens a `PartitionDivision`
  namespace.
- General objects use the names Mathlib would use: `MvPolynomial.macdonaldP`,
  `Nat.qBinomial`/`Polynomial`-valued q-analogues, `YoungDiagram.armLength`.
  Before naming a q-analogue, check Mathlib and open Mathlib PRs again.
- Only `Division/` uses the `PartitionDivision` namespace.
- Follow the workspace Lean style: Mathlib naming conventions, at most 100
  columns, `lia` for linear arithmetic, no `sorry`, axioms or opaque
  placeholders.

## Finite variables first

All symmetric-function statements are made in `MvPolynomial (Fin N) R` and
`MvPolynomial.symmetricSubalgebra`, as in Mathlib. The stable statement for
symmetric functions follows by taking `N` at least the degree; it does not
need an infinite-variable ring. If a stable ring is wanted for the public
statement, port `SymmetricFunction` from `rhodges-math/klebers-conjecture`
rather than building a new one.

## Reuse map

| Need | Source | Plan |
|---|---|---|
| `esymm`, `esymmPart`, `msymm`, `hsymm`, fundamental theorem | Mathlib | use directly |
| `msymm` coefficients, elementary expansions | Mathlib's fundamental theorem | new, `Mathlib/` (`ElementaryExpansion`, `Monomial`, `MonomialBasis`) |
| matrix trace, base change, `leftMulMatrix`, roots of unity, `NNRat` | Mathlib | use directly |
| finiteness of `MvPolynomial.expand` | Tau Ceti `RingTheory/MvPolynomial/Expand.lean` | port when the free basis needs it |
| hooks, arms, legs | Tau Ceti `Combinatorics/Young/HookLength/Basic.lean` | port |
| vertical strips | Tau Ceti `Combinatorics/Young/VerticalStrip.lean` | port |
| Schur polynomials and their Pieri rule | Tau Ceti `RingTheory/MvPolynomial/Symmetric/Schur/*` | port if the Macdonald layer specializes to Schur |
| dominance order | Tau Ceti `Combinatorics/Young/Dominance.lean`, Mathlib PR #42725 | not needed: the proof uses lexicographic order |
| nonnegative-coefficient polynomials, positive traces | none found | new, `Mathlib/` |
| exponent filter, root-of-unity average | none found | new, `Mathlib/` |
| `k`-restricted partitions and their decomposition | none found | new, `Mathlib/Combinatorics/` |
| q-analogues | none found in Mathlib or Tau Ceti | new, `QAnalog/` |
| Macdonald polynomials, Pieri coefficients, root-of-unity factorization | none found in any proof assistant | new, `Macdonald/` |

The survey behind this table (Mathlib at the v4.35.0 tag, Tau Ceti `main`,
`klebers-conjecture`, Coq-Combi, the Isabelle AFP) was run on 2026-10-17.
"None found" means not found, not proved absent.

## Porting rules

Tau Ceti tracks Mathlib `master` daily and does not pin the v4.35.0 tag, so a
Lake dependency would force this project onto Mathlib master. We port instead:

- copy the file to `PartitionDivision/TauCeti/<original path>`, keep its
  copyright header, and add a provenance line naming the Tau Ceti commit;
- change only what the Mathlib pin requires, and list the changes in the
  module docstring;
- record the file in `CREDITS.md`.

When Tau Ceti and this project agree on a Mathlib revision, or a ported file
reaches Mathlib, delete the port and import the original. Keeping the original
paths makes that a mechanical change.
