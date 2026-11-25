# Project S · P09 · Shellsort gap-table generation

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

Six roots cover prefix moments, a menu tail bound, pruning with a comparison budget, occupancy counts and conditional warm-start budgets. End-to-end planner complexity and inexpensive generation of an exact optimal table remain separate research claims.

The November 25 update adds an order-uniform conditional moment bound, replayable seven- and eight-pass comparison certificates, a census of product gap tables at one billion keys and exact all-winner searches through nine keys. [Results, conditions and reproduction](research/2026-11-25/README.md)

For the specified eight-pass table at one billion uniformly permuted keys, the mean exceeds 41,641,698,503 key comparisons. Its fourth pass alone has mean strictly between 5,135,574,733 and 5,287,379,676. Separate bounds cover all legal second gaps after the fixed first gap 62,500,000. The occupancy analysis also gives executable insertion and finite-law record moment bounds in Lean. [Finite certificates](research/2026-11-25/prefix-certificates.md) · [Occupancy and moments](research/2026-11-25/occupancy-grid.md) · [Formal statements](Shellsort/RecordMomentBounds.lean)

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). The [gap-table generator](https://github.com/EternalYMZ/Project-S/tree/main/playground) enumerates product tables from the length and two bases.
