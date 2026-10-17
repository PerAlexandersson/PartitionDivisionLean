# PartitionDivisionLean agent guide

Read the workspace Lean guide, this file, and `HANDOFF.md` before editing or
building. This repository is a public formalization project, separate from the
private `PartitionDivision` proof-audit repository. Do not copy the emailed
draft, Overleaf source, private audit files, or their Git history here.

The target is the unconditional elementary-positivity theorem stated in
`docs/PROOF_OUTLINE.md`. Name intermediate results by what they actually
prove; a positive-trace lemma or a conditional Macdonald theorem is not the
partition-division theorem. Do not use `sorry`, custom axioms, or opaque
placeholders for missing mathematical input.

One designated Lean worker owns source integration and all Lake builds.
Check `HANDOFF.md` and the active build owner before compiling. Use the
workspace `lake-workspace` wrapper and external build cache; never run plain
Lake against a manifest with relative `.lake` paths. Keep source files at
most 100 columns, use two-space indentation and `lia` for linear arithmetic.

Update the outline's source map and `HANDOFF.md` when a module or theorem is
implemented. Commit and push focused verified checkpoints. Public prose must
distinguish established paper results, checked Lean results, and open proof
obligations.
