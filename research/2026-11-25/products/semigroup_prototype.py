"""Finite semigroup support profiles for the Project S product-gap survey.

Public integration API
----------------------
intervals(a, b, K) -> [(L, U_or_None, holes), ...]
    Covers exactly the depths j >= a whose number of positive integers
    outside <a,b> up to j is <= K.  U=None is a permanent stable tail.

aggregate_weights(gaps, n) -> DepthWeights
    .full(L, U=None), .suffix(L, U=None) give numbers of actual insertion
    coordinates with depths in [L,U].  The suffix omits the first/largest
    gap.  .full_cumulative(J), .suffix_cumulative(J) count depths <= J.

For a complete descending product table and coprime a,b, the normalized
semigroup of ALL previous gaps is exactly <a,b>, on the relevant range
kg<n.  Without coprimality, <a,b> is a guaranteed subsemigroup, so the
same support truncation remains safe but need not use all prefix order.

At depth j<a use the old log correction.  On a returned interval use
log(1-t**(holes+1)).  At omitted depths j>=a use correction zero, an
UPPER bound because the true correction is negative.  All coefficients
returned here are nonnegative integers; directed logarithm rounding is
the caller's responsibility.  No allocation scales with n.
"""

from bisect import bisect_left
from dataclasses import dataclass
from heapq import heappop, heappush
from math import gcd
from typing import Iterable, Optional


def _bases(a: int, b: int) -> None:
    if not (isinstance(a, int) and isinstance(b, int) and 2 <= a < b):
        raise ValueError("Require integer bases 2 <= a < b.")


def two_generator_contains(k: int, a: int, b: int) -> bool:
    """Exact membership in <a,b>, including 0; works without coprimality."""
    _bases(a, b)
    if k < 0:
        return False
    d = gcd(a, b)
    if k % d:
        return False
    aa, bb, kk = a // d, b // d, k // d
    if aa == 1:
        return True
    residue_coefficient = ((kk % aa) * pow(bb, -1, aa)) % aa
    return kk >= bb * residue_coefficient


def holes_count(j: int, a: int, b: int) -> int:
    """Number of k in [1,j] outside <a,b>, using its small Apery set."""
    _bases(a, b)
    if j <= 0:
        return 0
    d = gcd(a, b)
    aa, bb, limit = a // d, b // d, j // d
    # The aa values bb*s, 0<=s<aa, are the Apery set, in a permuted
    # residue order.  The s=0 stream includes zero, which is subtracted.
    members_with_zero = sum(
        (limit - bb * s) // aa + 1
        for s in range(aa) if bb * s <= limit
    )
    return j - (members_with_zero - 1)


def first_holes(a: int, b: int, count: int) -> list[int]:
    """First `count` nonmembers; fewer exactly when the holes are exhausted.

    Coprime case: merge at most a-1 finite arithmetic streams from the
    Apery set, using O(a+count) storage and O((a+count) log a) time.
    Noncoprime case: direct checking stops within 2*count integers, since
    at least half of all integers fail the divisibility condition.
    """
    _bases(a, b)
    if count < 0:
        raise ValueError("count must be nonnegative")
    if count == 0:
        return []
    d = gcd(a, b)
    if d > 1:
        aa, bb = a // d, b // d
        inverse = pow(bb, -1, aa) if aa > 1 else 0
        out = []
        k = 1
        while len(out) < count:
            if k % d:
                out.append(k)
            else:
                kk = k // d
                if kk < bb * (((kk % aa) * inverse) % aa):
                    out.append(k)
            k += 1
        assert k - 1 <= 2 * count
        return out
    inverse = pow(b, -1, a)
    heap = []
    for r in range(1, a):
        apery = b * ((inverse * r) % a)
        # Every r<a is a hole because a is the smallest generator.
        assert apery > r
        heappush(heap, (r, apery))
    out = []
    while heap and len(out) < count:
        value, limit = heappop(heap)
        out.append(value)
        following = value + a
        if following < limit:
            heappush(heap, (following, limit))
    return out


def intervals(a: int, b: int, K: int) -> list[tuple[int, Optional[int], int]]:
    """Return [L,U] runs with j>=a and holes_count(j,a,b)<=K.

    Every returned interval has q_j>0.  Consequently the restricted
    partition function is t/(1-t) * (1-t**(holes+1)).  An omitted tail
    may be bounded above by t/(1-t); no unspecified monotonicity is used.
    """
    _bases(a, b)
    if not isinstance(K, int) or K < 0:
        raise ValueError("K must be a nonnegative integer")
    gaps = first_holes(a, b, K + 1)
    genus = (a - 1) * (b - 1) // 2 if gcd(a, b) == 1 else None
    result = []
    for holes in range(1, min(K, len(gaps)) + 1):
        lo = max(a, gaps[holes - 1])
        if holes < len(gaps):
            hi = gaps[holes] - 1
        else:
            # Reaching the end without a next hole is justified ONLY
            # when all holes of the coprime numerical semigroup occur.
            assert genus == holes and genus <= K
            hi = None
        if hi is None or lo <= hi:
            result.append((lo, hi, holes))
    return result


semigroup_intervals = intervals


@dataclass(frozen=True)
class DepthWeights:
    """Exact integer coordinate counts for a full table and its suffix."""

    n: int
    ascending: tuple[int, ...]
    prefix_sums: tuple[int, ...]
    first_gap: int

    @property
    def full_total(self) -> int:
        return len(self.ascending) * self.n - self.prefix_sums[-1]

    @property
    def suffix_total(self) -> int:
        return self.full_total - (self.n - self.first_gap)

    def full_cumulative(self, J: int) -> int:
        """B(J)=sum_g min(J*g, n-g), with B(J)=0 for J<=0."""
        if J <= 0:
            return 0
        threshold = (self.n + J) // (J + 1)  # ceil(n/(J+1))
        split = bisect_left(self.ascending, threshold)
        small_sum = self.prefix_sums[split]
        large_sum = self.prefix_sums[-1] - small_sum
        large_count = len(self.ascending) - split
        return J * small_sum + large_count * self.n - large_sum

    def suffix_cumulative(self, J: int) -> int:
        if J <= 0:
            return 0
        return self.full_cumulative(J) - min(J * self.first_gap,
                                             self.n - self.first_gap)

    def full(self, L: int, U: Optional[int] = None) -> int:
        if L < 1 or (U is not None and U < L):
            raise ValueError("Require 1 <= L <= U, or U=None")
        upper = self.full_total if U is None else self.full_cumulative(U)
        return upper - self.full_cumulative(L - 1)

    def suffix(self, L: int, U: Optional[int] = None) -> int:
        if L < 1 or (U is not None and U < L):
            raise ValueError("Require 1 <= L <= U, or U=None")
        upper = self.suffix_total if U is None else self.suffix_cumulative(U)
        return upper - self.suffix_cumulative(L - 1)


def aggregate_weights(gaps: Iterable[int], n: int) -> DepthWeights:
    """Validate a descending table and build O(p)-space count queries.

    Each query uses a binary search, O(log p) time.  No membership claim
    about the supplied table is made; the caller verifies that it is the
    complete product table before invoking the product-prefix theorem.
    """
    gaps = tuple(gaps)
    if not isinstance(n, int) or n < 2:
        raise ValueError("n must be an integer >=2")
    if not gaps or any(not isinstance(g, int) or not 1 <= g < n for g in gaps):
        raise ValueError("Require a nonempty table with integer 1<=g<n")
    if any(left <= right for left, right in zip(gaps, gaps[1:])):
        raise ValueError("Require strictly descending gaps")
    ascending = tuple(reversed(gaps))
    sums = [0]
    for g in ascending:
        sums.append(sums[-1] + g)
    return DepthWeights(n, ascending, tuple(sums), gaps[0])


def product_gaps(n: int, a: int, b: int) -> list[int]:
    """Small independent exact generator, for validation and tests."""
    _bases(a, b)
    values = set()
    av = 1
    while av < n:
        value = av
        while value < n:
            values.add(value)
            value *= b
        av *= a
    return sorted(values, reverse=True)


def self_check() -> dict[str, int]:
    """Finite regression checks; no n=1e9 array or sorting experiment."""
    membership_cases = interval_cases = weight_cases = prefix_cases = 0
    for a in range(2, 13):
        for b in range(a + 1, 18):
            limit = 500
            reachable = [False] * (limit + 1)
            reachable[0] = True
            for k in range(1, limit + 1):
                reachable[k] = ((k >= a and reachable[k-a]) or
                                (k >= b and reachable[k-b]))
            missing = 0
            for k in range(limit + 1):
                assert two_generator_contains(k, a, b) == reachable[k]
                missing += int(k > 0 and not reachable[k])
                assert holes_count(k, a, b) == missing
                membership_cases += 1
            for K in (0, 1, 3, 10, 64, 512):
                runs = intervals(a, b, K)
                for j in range(1, limit + 1):
                    containing = [h for lo, hi, h in runs
                                  if lo <= j and (hi is None or j <= hi)]
                    expected = holes_count(j, a, b)
                    assert containing == ([expected]
                        if j >= a and expected <= K else [])
                    interval_cases += 1
            for n in (17, 51, 100):
                table = product_gaps(n, a, b)
                weights = aggregate_weights(table, n)
                direct = [0] * n
                suffix = [0] * n
                for index, g in enumerate(table):
                    for j in range(1, n):
                        number = min(g, max(0, n - j * g))
                        direct[j] += number
                        if index:
                            suffix[j] += number
                full_sum = suffix_sum = 0
                for j in range(1, n):
                    full_sum += direct[j]
                    suffix_sum += suffix[j]
                    assert weights.full(j, j) == direct[j]
                    assert weights.suffix(j, j) == suffix[j]
                    assert weights.full_cumulative(j) == full_sum
                    assert weights.suffix_cumulative(j) == suffix_sum
                    weight_cases += 1
                assert weights.full(1) == sum(direct)
                assert weights.suffix(1) == sum(suffix)
                # Exact full-prefix membership, tested only when coprime.
                if gcd(a, b) == 1:
                    prefix_reachable = [False] * n
                    prefix_reachable[0] = True
                    for g in table:
                        for k in range(1, (n - 1) // g + 1):
                            assert prefix_reachable[k*g] == two_generator_contains(k,a,b)
                            prefix_cases += 1
                        for distance in range(g, n):
                            if prefix_reachable[distance-g]:
                                prefix_reachable[distance] = True
    return dict(membership_cases=membership_cases,
                interval_cases=interval_cases,
                weight_cases=weight_cases,
                prefix_cases=prefix_cases)


if __name__ == "__main__":
    import json
    print(json.dumps(self_check(), sort_keys=True))
