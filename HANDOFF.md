# PartitionDivisionLean handoff

## Current status

The public project is at
`https://github.com/PerAlexandersson/PartitionDivisionLean` on `main`.
GitHub reports public visibility, and the initial checkpoint `0012cc7` was
pushed and returned HTTP 200. It contains a mathematical and Lean proof
outline only.
There is no Lean package, compiled declaration, or formalization claim yet.
The private `PartitionDivision` audit repository and the unpublished companion
manuscript are not part of this Git history.

2026-10-17: the user prioritized this project. The Claude Code session that also
integrates RealRooted owns source integration and the shared Lake build slot; workers draft
in scratch directories and never run Lake. Build with
`lake-workspace build PartitionDivision` (Lean/Mathlib v4.35.0, same shared package checkouts as
RealRooted; build output in `/lake-cache/ai-projects/build/PartitionDivision`).
The host supervisor has released the initial README, guide, outline, and
handoff after the public checkpoint. The only subsequent change to this file
records its publication status.

2026-10-17 (later): `docs/ARCHITECTURE.md` fixes the module layers (`Mathlib/`, `TauCeti/`,
`QAnalog/`, `Macdonald/`, `Division/`) and the reuse map; the work is split into issues #1–#14
with roadmap #15. Drafts in progress in the integrator's scratch workers (nothing integrated yet):
#2 nonnegative coefficients and positive traces, #3/#4 exponent filter and root average, #7 Tau Ceti
port of hooks and vertical strips, #9 Macdonald design note. Ported code keeps its copyright header
and a provenance line, and is listed in `CREDITS.md`.

## First implementation checkpoint

Choose a pinned Lean/Mathlib toolchain compatible with the shared cache, then
formalize the finite exponent filter and the unconditional positive-matrix
trace kernel. Verify focused modules and their axiom inventory before
starting Macdonald-polynomial infrastructure. The root-of-unity factorization
and the unpaired Pieri terms identified in the outline remain explicit proof
obligations.
