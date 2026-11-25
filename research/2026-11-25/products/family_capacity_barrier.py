#!/usr/bin/env python3
"""Certify an artificial-record capacity barrier for the unexcluded family.

This is NOT a Shellsort upper bound and does not claim that the artificial
records are jointly realizable by actual sorting executions.  It exhibits
independent record laws inside the complete coordinatewise semigroup support,
with the true first-pass law, total expected comparisons <50*n, and entropy
>log(n!).  Therefore that support/entropy/cost relaxation, even with distinct
Gibbs temperatures at every coordinate, cannot exclude a certified table.

All certification uses Fraction and integer outward bounds.  A previously
computed floating proposal chooses rational temperatures only.  It has no
role in accepting a certificate.

Suffix law: q_j=0,j<=CAP uses m=0..j with c=1+min(m,j-1).
Otherwise use m=0..min(CAP,j-q_j) if q_j>0, or m=0..CAP if q_j=0.
On every selected support put probability proportional to t**c.
The initial pass has independent uniform insertion digits m=0..j.

Exact-entropy variant: interpolate EACH suffix marginal toward delta_(m=0).
The resulting product law has entropy continuous from zero to the certified
suffix entropy and expected cost no larger than the certified cost.  Thus
the exact required entropy can also be attained, keeping the first law fixed.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
import time

from semigroup_prototype import aggregate_weights, intervals, product_gaps


ROOT = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "family_barrier_legacy", ROOT / "source/evaluate_gap_lower_bounds.py")
legacy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(legacy)
SCALE = legacy.SCALE
CAP = 64


def floor_q(x):
    return x.numerator // x.denominator


def ceil_q(x):
    return -((-x.numerator) // x.denominator)


@lru_cache(None)
def log_one_plus_bounds(y):
    """Directed rational atanh series, including its signed remainder."""
    y = F(y)
    assert y > -1
    if not y:
        return 0, 0
    if abs(y) <= F(1, 10**12):
        # The absolute tail of log(1+y) after y is at most
        # y^2/(2*(1-|y|)); also log(1+y)<=y for y>-1.
        lo = y - y*y / (2*(1-abs(y)))
        return floor_q(lo*SCALE), ceil_q(y*SCALE)
    v = y / (2+y)
    v2, power, total, j = v*v, v, F(0), 0
    while True:
        total += power / (2*j+1)
        power *= v2
        remainder = 2*abs(power) / ((2*j+3)*(1-v2))
        if remainder*SCALE < 1:
            break
        j += 1
    if v > 0:
        lo, hi = 2*total, 2*total+remainder
    else:
        lo, hi = 2*total-remainder, 2*total
    return floor_q(lo*SCALE), ceil_q(hi*SCALE)


def law_coefficient(mean, correction, t, minus_log_t_lower, log_one_minus_t_upper):
    """Outward mean upper and Shannon entropy lower for one coordinate."""
    assert mean >= 1
    corr_lower, corr_upper = log_one_plus_bounds(correction)
    # H = -log(1-t) + log(1+correction) + (mean-1)*log(1/t).
    entropy_lower = (-log_one_minus_t_upper + corr_lower
                     + floor_q((mean-1)*minus_log_t_lower))
    return {
        "mean_upper_scaled": ceil_q(mean*SCALE),
        "entropy_lower_scaled": entropy_lower,
        "log_correction_lower_scaled": corr_lower,
        "log_correction_upper_scaled": corr_upper,
    }


@lru_cache(None)
def temperature_coefficients(t):
    """Only CAP+1 geometric laws and CAP finite record-minimum laws."""
    t = F(t)
    assert 0 < t < 1
    lt = legacy.log_bounds(t)
    l1 = legacy.log_bounds(1-t)
    L_lower = -lt[1]
    assert L_lower > 0
    old, geometric = {}, {}
    A, B, power = F(0), F(0), F(1)
    for d in range(CAP+1):
        A += power
        B += d*power
        mean = 1+B/A
        geometric[d] = law_coefficient(mean, -power*t, t, L_lower, l1[1])
        assert SCALE <= geometric[d]["mean_upper_scaled"] <= (d+1)*SCALE
        if d < CAP:
            j = d+1
            # Compared with weights (1,t,...,t^(j-1)), the unrestricted
            # insertion alphabet has one extra digit at cost j.
            old_mean = 1+(B+d*power)/(A+power)
            old[j] = law_coefficient(old_mean, (1-2*t)*power, t,
                                     L_lower, l1[1])
        power *= t
    assert geometric[0]["mean_upper_scaled"] == SCALE
    assert geometric[0]["entropy_lower_scaled"] <= 0
    assert old[1]["mean_upper_scaled"] == SCALE
    assert old[1]["entropy_lower_scaled"] <= legacy.LN2[1]
    return {"t":str(t), "log_t_bounds_scaled":lt,
            "log_one_minus_t_bounds_scaled":l1,
            "old":old, "geometric":geometric}


def support_weights(row, n):
    a, b, gaps = row["a"], row["b"], row["gaps"]
    assert gcd(a,b) == 1
    assert gaps == product_gaps(n,a,b)
    agg = aggregate_weights(gaps,n)
    old = {j:agg.suffix(j,j) for j in range(1,min(a-1,CAP)+1)}
    old = {j:w for j,w in old.items() if w}
    geometric = {}
    for L,U,holes in intervals(a,b,CAP-1):
        w = agg.suffix(L,U)
        if w:
            geometric[holes] = geometric.get(holes,0)+w
    covered = sum(old.values())+sum(geometric.values())
    assert covered <= agg.suffix_total
    # On every remaining coordinate either j>CAP and q_j=0, or
    # q_j>0 and holes>=CAP.  The same 0..CAP geometric alphabet fits.
    geometric[CAP] = agg.suffix_total-covered
    assert sum(old.values())+sum(geometric.values()) == agg.suffix_total
    return {"old":old,"geometric":geometric,"suffix_coordinates":agg.suffix_total}


def prepare_first(n,rows):
    maximum = max(n//r["gaps"][0] for r in rows)
    logs = [(0,0)]+[legacy.log_bounds(F(i)) for i in range(1,maximum+2)]
    factorial_lower = [0]
    harmonics = [F(0)]
    for i in range(1,maximum+2):
        factorial_lower.append(factorial_lower[-1]+logs[i][0])
        harmonics.append(harmonics[-1]+F(1,i))
    return logs,factorial_lower,harmonics


def first_statistics(row,n,prepared):
    logs, factorial_lower, harmonics = prepared
    first = row["gaps"][0]
    m,r = divmod(n,first)
    # Uniform independent insertion digits, with their true comparison cost.
    mean = first*(F(m*(m-1),4)+m-harmonics[m]) + r*(F(m,2)+1-F(1,m+1))
    entropy_lower = first*factorial_lower[m]+r*logs[m+1][0]
    return {"chain_length_floor":m,"long_chains":r,
            "mean_exact":str(mean),"mean_upper_scaled":ceil_q(mean*SCALE),
            "entropy_lower_scaled":entropy_lower}


def certify_at_temperature(row,n,weights,first,t,log_factorial_upper):
    coeff = temperature_coefficients(t)
    mean_upper = first["mean_upper_scaled"]
    entropy_lower = first["entropy_lower_scaled"]
    for kind in ("old","geometric"):
        for index,weight in weights[kind].items():
            c = coeff[kind][index]
            mean_upper += weight*c["mean_upper_scaled"]
            entropy_lower += weight*c["entropy_lower_scaled"]
    return {"t":str(t),
            "expected_cost_upper_scaled":mean_upper,
            "record_entropy_lower_scaled":entropy_lower,
            "cost_margin_lower_scaled":50*n*SCALE-mean_upper,
            "entropy_surplus_lower_scaled":entropy_lower-log_factorial_upper,
            "passed":mean_upper<50*n*SCALE and entropy_lower>log_factorial_upper}


def scaled_decimal(integer,places=9,upper=False):
    """Display fixed-point bounds without passing through binary float."""
    factor = 10**places
    q = (-((-integer*factor)//SCALE) if upper else (integer*factor)//SCALE)
    sign = "-" if q<0 else ""
    q = abs(q)
    return f"{sign}{q//factor}.{q%factor:0{places}d}"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit",type=int,default=0,
                        help="Optional smoke subset, nearest proposed budget first")
    parser.add_argument("--output",type=Path,default=ROOT/"data/family_capacity_barrier.json")
    args = parser.parse_args()
    started = time.monotonic()
    n = 10**9
    source = ROOT/"source/gap_lower_bounds.jsonl"
    proposals_path = ROOT/"data/all_remaining_temperature_proposals.json"
    rows = [json.loads(line) for line in source.read_text().splitlines() if line.strip()]
    selected = {(r["a"],r["b"]):r for r in rows if r["coprime"]
                and r["certified_comparison_lower_bound"]<=50*n}
    proposals = json.loads(proposals_path.read_text())["proposals"]
    assert {(r["a"],r["b"]) for r in proposals} == set(selected)
    expected_rows = len(selected)
    if args.limit:
        proposals = sorted(proposals,key=lambda r:F(str(r["exploratory_bound_per_key"])),
                           reverse=True)[:args.limit]
    prepared = prepare_first(n,rows)
    # Integral upper bound: log(n!) <= (n+1)*log(n)-n+1.
    ln_n = legacy.log_bounds(F(n))
    log_factorial_upper = (n+1)*ln_n[1]-(n-1)*SCALE
    witnesses, unresolved, used_temperatures = [],[],set()
    retries = 0
    for number,proposal in enumerate(proposals,1):
        key = proposal["a"],proposal["b"]
        row = selected[key]
        weights = support_weights(row,n)
        first = first_statistics(row,n,prepared)
        suggestion = F(proposal["proposed_rational_t"])
        attempts = []
        for denominator in (100,1000,10000,100000,1000000):
            t = F(floor_q(suggestion*denominator)+1,denominator)
            if t in [F(x["t"]) for x in attempts]:
                continue
            assert suggestion < t < 1
            trial = certify_at_temperature(row,n,weights,first,t,log_factorial_upper)
            attempts.append(trial)
            if trial["passed"]:
                break
        retries += len(attempts)-1
        if not attempts[-1]["passed"]:
            unresolved.append({"a":key[0],"b":key[1],"attempts":attempts})
        else:
            witness = attempts[-1]
            used_temperatures.add(F(witness["t"]))
            witness.update({"a":row["a"],"b":row["b"],"passes":row["passes"],
                "table_sha256":row["table_sha256"],
                "proposal_only_t":proposal["proposed_rational_t"],
                "rational_temperature_attempts":len(attempts),
                "first":first,"suffix_support_counts":weights,
                "expected_cost_upper_decimal":scaled_decimal(witness["expected_cost_upper_scaled"],upper=True),
                "expected_cost_per_key_upper_decimal":scaled_decimal(
                    ceil_q(F(witness["expected_cost_upper_scaled"],n)),upper=True),
                "entropy_surplus_lower_decimal":scaled_decimal(witness["entropy_surplus_lower_scaled"]),
                "cost_margin_lower_decimal":scaled_decimal(witness["cost_margin_lower_scaled"])})
            witnesses.append(witness)
        if number%1000==0:
            print(json.dumps({"processed":number,"passed":len(witnesses),
                              "unresolved":len(unresolved),"temperature_cache":temperature_coefficients.cache_info().currsize,
                              "seconds":round(time.monotonic()-started,2)}),flush=True)
    all_passed = len(witnesses)==len(proposals) and not unresolved
    global_claim = all_passed and not args.limit and len(proposals)==expected_rows
    worst_cost = max(witnesses,key=lambda w:w["expected_cost_upper_scaled"]) if witnesses else None
    min_entropy = min(witnesses,key=lambda w:w["entropy_surplus_lower_scaled"]) if witnesses else None
    coefficients = [temperature_coefficients(t) for t in sorted(used_temperatures)]
    report = {
        "status":"CERTIFIED" if all_passed else "PARTIAL; SEE UNRESOLVED",
        "n":n,"scale":str(SCALE),"cap":CAP,
        "family_size":expected_rows,"checked_rows":len(proposals),"certified_rows":len(witnesses),
        "entire_remaining_family_certified":global_claim,
        "statement":"For each certified row there exists an artificial independent record law inside the exact complete-prefix coordinate supports, with the true first-pass mean and entropy, expected total comparisons <50*n, and record entropy >log(n!).",
        "method_boundary":"This defeats the support+entropy+cost relaxation at every common or coordinatewise temperature. It is not a Shellsort upper bound, not a realizable sorting-record claim, and not an obstruction to using joint record/state structure.",
        "exact_entropy_extension":"Mix each suffix marginal continuously with the point mass at m=0. The product entropy runs continuously from zero to the certified suffix entropy, while its mean cost never exceeds the certified cost. Keeping the first-pass law fixed gives a law with exactly total entropy log(n!) and still cost <50*n.",
        "log_factorial_upper_formula":"(n+1)*log(n)-n+1",
        "log_n_bounds_scaled":ln_n,"log_factorial_upper_scaled":log_factorial_upper,
        "arithmetic":"Fraction for all probabilities and moments; signed rational atanh series with explicit remainder and outward integer rounding for all logarithms; floating proposals never enter a certificate inequality.",
        "rational_temperature_count":len(used_temperatures),"refinement_retries":retries,
        "maximum_expected_cost_witness":worst_cost,
        "minimum_entropy_surplus_witness":min_entropy,
        "source_sha256":{str(p.relative_to(ROOT)):sha256(p) for p in
            (source,proposals_path,ROOT/"semigroup_prototype.py",Path(__file__).resolve())},
        "coefficients":coefficients,"witnesses":witnesses,"unresolved":unresolved,
        "elapsed_seconds":round(time.monotonic()-started,3),
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,ensure_ascii=False,separators=(",",":"))+"\n")
    print(json.dumps({k:report[k] for k in ("status","checked_rows","certified_rows",
        "entire_remaining_family_certified","rational_temperature_count","refinement_retries","elapsed_seconds")},ensure_ascii=False))
    if worst_cost:
        print(json.dumps({"largest_cost":[worst_cost["a"],worst_cost["b"]],
                          "t":worst_cost["t"],"cost_upper":worst_cost["expected_cost_upper_decimal"],
                          "cost_margin_lower":worst_cost["cost_margin_lower_decimal"],
                          "entropy_surplus_lower":worst_cost["entropy_surplus_lower_decimal"]}))
    if min_entropy:
        print(json.dumps({"smallest_entropy_margin":[min_entropy["a"],min_entropy["b"]],
                          "t":min_entropy["t"],"entropy_surplus_lower":min_entropy["entropy_surplus_lower_decimal"]}))
    if unresolved:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
