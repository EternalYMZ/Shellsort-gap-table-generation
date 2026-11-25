"""Exact counts for the six-key collision and record-moment examples."""
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial


def gap_pass(keys, gap):
    keys = list(keys)
    comparisons = 0
    for i in range(gap, len(keys)):
        key = keys[i]
        j = i
        while j >= gap:
            comparisons += 1
            if keys[j - gap] <= key:
                break
            keys[j] = keys[j - gap]
            j -= gap
        keys[j] = key
    return keys, comparisons


def check_collisions():
    for bins in range(1, 6):
        totals = [0, 0, 0]
        for labels in product(range(bins), repeat=6):
            first, _ = gap_pass(labels, 5)
            second, _ = gap_pass(first, 4)
            for j in range(3):
                totals[j] += second[j] == second[j + 3]
        observed = F(sum(totals), bins ** 6)
        formula = F(3, bins) + F((bins - 1) * (bins - 2), 6 * bins ** 3)
        assert observed == formula
        if bins == 3:
            assert totals == [243, 252, 243]
        print(f"G={bins}  E A_3={observed}")


def record_interval(length, mean, factorial_second):
    if mean == 0:
        return F(1), F(1)
    k = int(1 + factorial_second / mean)
    low = max(F(0), 1 - mean + factorial_second / length)
    high = 1 - 2 * mean / (k + 1) + factorial_second / (k * (k + 1))
    return low, high


def check_records():
    n = 6
    samples = factorial(n)
    sums = [0] * n
    pairs = [0] * n
    records = [0] * n
    comparison_sum = 0
    for keys in permutations(range(n)):
        first, c1 = gap_pass(keys, 4)
        result, c2 = gap_pass(first, 1)
        assert c1 == 2 and result == list(range(n))
        comparison_sum += c1 + c2
        charges = []
        for i, key in enumerate(first):
            smaller = sum(prior < key for prior in first[:i])
            sums[i] += smaller
            pairs[i] += smaller * (smaller - 1)
            records[i] += smaller == 0
            charges.append(i - smaller + 1 - (smaller == 0))
        assert sum(charges) == c2

    mean_only_low = mean_only_high = low = high = F(2)
    for i in range(n):
        mean, second = F(sums[i], samples), F(pairs[i], samples)
        actual = F(records[i], samples)
        if i >= 4:
            # The earlier 4-chain predecessor is already smaller.
            mlo = mhi = rlo = rhi = F(0)
        elif i == 0:
            mlo = mhi = rlo = rhi = F(1)
        else:
            mlo, mhi = max(F(0), 1 - mean), 1 - mean / i
            rlo, rhi = record_interval(i, mean, second)
        assert mlo <= rlo <= actual <= rhi <= mhi
        if i == 3:
            assert (mean, second, rlo, rhi) == (F(11, 6), F(41, 15), F(7, 90), F(7, 30))
        mean_only_low += i - mean + 1 - mhi
        mean_only_high += i - mean + 1 - mlo
        low += i - mean + 1 - rhi
        high += i - mean + 1 - rlo
    mean_only = (mean_only_low, mean_only_high)
    assert mean_only == (F(185, 18), F(11))
    assert (low, high) == (F(317, 30), F(193, 18))
    exact = F(comparison_sum, samples)
    center = (low + high) / 2
    radius_per_tag = (high - low) / (2 * n)
    residual = (center - exact) / n
    assert (center, radius_per_tag, residual, exact) == (F(479, 45), F(7, 540), F(1, 540), F(319, 30))
    print(f"H=(4,1)  mean-only={mean_only_low}..{mean_only_high}  two moments={low}..{high}")
    print(f"exact={exact}  true residual per tag={residual}  radius per tag={radius_per_tag}")


if __name__ == "__main__":
    check_collisions()
    check_records()
