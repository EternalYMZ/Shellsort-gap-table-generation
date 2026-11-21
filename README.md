# Project S · P09 · Shellsort gap-table generation

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

Six roots cover prefix moments, a menu tail bound, pruning with a comparison budget, occupancy counts and conditional warm-start budgets. End-to-end planner complexity and inexpensive generation of an exact optimal table remain separate research claims.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). The [gap-table generator](https://github.com/EternalYMZ/Project-S/tree/main/playground) enumerates product tables from the length and two bases.
