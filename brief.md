# Certifying a gap table before sorting

For fixed $n$, let $C(w,\pi)$ count actual key comparisons under a predetermined table and a uniform input permutation. A gap-$h$ pass must visit $n-h$ noninitial chain slots. Each visit compares at least once, even on sorted input. Consequently
$$S(w)=\sum_{h\in w}(n-h)\le\mathbb E_\pi C(w,\pi).$$
Given an incumbent of mean at most $B$, discard candidates with $S(w)>B$. Equality cannot improve the incumbent, but may hide a tied winner. Keeping equality preserves all possible ties. Lean gives a pruning certificate preserving the exact minimum.

For the different task of finding a table of mean order $n\log n$, a constant-factor loss is acceptable. Draw candidate tables from the specified family and score them on permutations independent of the future input. Capping a trial's comparisons can make a table with rare expensive inputs appear cheap. Higher moments of squared displacement at block boundaries bound the proportion of candidates with large tails and control truncation loss. Drawing a table and drawing a test permutation are distinct random choices.

The public formal results include the moment estimates and pruning theorem. The full planning cost of randomized selection is studied analytically. Cheap exact minimization for every size and convergence of the optimal leading coefficient remain separate problems.

[OptimalScanPruning.lean](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/OptimalScanPruning.lean) · [ActualMenuMoment.lean](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/ActualMenuMoment.lean) · [PredrawnMenuMoment.lean](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/PredrawnMenuMoment.lean)
