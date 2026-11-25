#!/usr/bin/env python3
"""Certify selected rational temperature refinements, separately from support.

Selection: the 24 old unexcluded coprime rows with lower bound >=48 billion,
plus four previously discussed examples.  Optimization proposes a rational
witness; only Fraction/interval/integer calculations establish its bound.
"""
import json
from pathlib import Path
import time
import argparse
import evaluate_semigroup_bounds as cert


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--propose',action='store_true',help='Propose fresh witnesses with optional numpy/scipy instead of replaying saved rational temperatures.')
    args=parser.parse_args()
    start=time.monotonic()
    rows=cert.read_jsonl(cert.ROOT/'data/semigroup_gap_lower_bounds.jsonl')
    source=cert.read_jsonl(cert.ROOT/'source/gap_lower_bounds.jsonl')
    prepared=cert.prepared_from_source(10**9,source)
    selected={(11,12),(29,33),(8,179),(182,183)}
    selected.update((r['a'],r['b']) for r in source if r['coprime'] and
                    48_000_000_000<=r['certified_comparison_lower_bound']<=50_000_000_000)
    witnesses=[]
    coefficients=[]
    output=[]
    saved_path=cert.ROOT/'data/selected_temperature_certificates.json'
    saved={}
    if not args.propose and saved_path.exists():
        saved={(r['a'],r['b']):r['selected_refinement_rational_t']
               for r in json.loads(saved_path.read_text())['witnesses']}
    if args.propose or not saved:
        from scipy.optimize import minimize_scalar
        from explore_temperatures import objective
    for row in rows:
        if (row['a'],row['b']) not in selected:
            output.append(row)
            continue
        weights=cert.make_weights(row,10**9)
        if (row['a'],row['b']) in saved:
            td=saved[(row['a'],row['b'])]
        else:
            lower=objective(row,10**9,prepared,weights)
            proposed=minimize_scalar(lambda t:-lower(t),bounds=(0.002,0.96),method='bounded',options={'xatol':1e-11})
            td=f'{proposed.x:.6f}'
        coeff=cert.restriction_coefficients(td)
        ev=cert.evaluate_temperature(row,10**9,prepared,weights,coeff)
        old_refined=max(row['previous_certified_comparison_lower_bound'],ev['old'])
        final=max(row['semigroup_original_grid_lower_bound'],ev['new'],old_refined)
        out=dict(row)
        out.update({'selected_refinement_rational_t':td,
                    'selected_refinement_old_capacity_bound':ev['old'],
                    'selected_refinement_semigroup_capacity_bound':ev['new'],
                    'temperature_refinement_without_semigroup_lower_bound':old_refined,
                    'certified_comparison_lower_bound':final,
                    'certified_per_key':final/10**9,
                    'strictly_above_50_billion':final>50_000_000_000,
                    'strictly_above_53_billion':final>53_000_000_000,
                    'at_least_200_billion':final>=200_000_000_000})
        if final>row['semigroup_original_grid_lower_bound']:
            out.update({'new_best_t':td,'new_best_certificate_kind':'semigroup_selected_rational_temperature'})
        output.append(out)
        keys=('a','b','passes','previous_certified_comparison_lower_bound','semigroup_original_grid_lower_bound',
              'temperature_refinement_without_semigroup_lower_bound','selected_refinement_semigroup_capacity_bound',
              'selected_refinement_rational_t','certified_comparison_lower_bound')
        witnesses.append({k:out[k] for k in keys})
        coefficients.append(coeff)
    destination=cert.ROOT/'data'
    (destination/'selected_temperature_certificates.json').write_text(json.dumps({
        'n':10**9,'selection_rule':'Old-unexcluded coprime lower bound >=48 billion; four named examples.',
        'certified_rows':len(witnesses),'witnesses':witnesses,
        'new_exclusions':sum(r['previous_certified_comparison_lower_bound']<=50_000_000_000<r['certified_comparison_lower_bound'] for r in witnesses),
        'arithmetic':'Exact rational and integer outward bounds; scipy used only to propose witnesses.',
        'elapsed_seconds':time.monotonic()-start},indent=2)+'\n')
    (destination/'selected_temperature_coefficients.json').write_text(json.dumps({'coefficients':coefficients},indent=2)+'\n')
    (destination/'combined_gap_lower_bounds.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in output))
    summary=cert.summarize(output,time.monotonic()-start)
    summary['selected_refinement_rows']=len(witnesses)
    (destination/'combined_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'rows':len(witnesses),'examples':summary['specified_examples'],
                      'total':summary['total'],'seconds':time.monotonic()-start},indent=2))


if __name__=='__main__':
    main()
