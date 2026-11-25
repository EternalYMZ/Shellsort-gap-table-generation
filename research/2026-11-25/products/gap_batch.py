#!/usr/bin/env python3
"""Enumerate integer-base product gap tables using the supplied generator."""
from pathlib import Path
import argparse
import csv
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from math import gcd, ceil
import shutil
import statistics
import time


def summarize(rows):
    values=sorted(r['passes'] for r in rows)
    def quantile(q):
        return values[max(0,ceil(q*len(values))-1)]
    counts=Counter(values)
    return {
        'count':len(rows), 'unique_tables':len({r['table_sha256'] for r in rows}),
        'min':min(values), 'max':max(values), 'mean':statistics.mean(values),
        'median':statistics.median(values),
        'nearest_rank_quantiles':{str(q):quantile(q) for q in (.05,.1,.25,.5,.75,.9,.95)},
        'modes':[v for v,c in sorted(counts.items()) if c==max(counts.values())],
        'histogram':dict(sorted(counts.items())),
        'bands':{f'{lo}-{hi}':sum(lo<=v<=hi for v in values)
                 for lo,hi in [(0,8),(9,19),(20,29),(30,39),(40,49),(50,99),(100,1000)]},
        'exact_lengths':{str(k):counts[k] for k in (8,26,40,45)},
        'near_26_24_through_28':sum(24<=v<=28 for v in values),
        'mandatory_comparison_min':min(r['mandatory_comparisons'] for r in rows),
        'mandatory_comparison_max':max(r['mandatory_comparisons'] for r in rows),
    }


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,default=10**9)
    parser.add_argument('--max-base',type=int,default=183)
    parser.add_argument('--source',type=Path,default=Path(__file__).resolve().parent/'source'/'product_gaps.py')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'data')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    spec=importlib.util.spec_from_file_location('supplied_product_gaps',args.source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    started=time.perf_counter()
    records=[]
    def record(a,b):
        gaps=module.product_gaps(args.n,a,b)
        assert gaps==sorted(set(gaps),reverse=True) and gaps[-1]==1
        assert all(1<=h<args.n for h in gaps)
        total=sum(gaps);p=len(gaps)
        return {'n':args.n,'a':a,'b':b,'gcd':gcd(a,b),'coprime':gcd(a,b)==1,
                'passes':p,'sum_gaps':total,'mandatory_comparisons':p*args.n-total,
                'largest_gap':gaps[0],
                'table_sha256':hashlib.sha256(','.join(map(str,gaps)).encode()).hexdigest(),
                'gaps':gaps}
    with (args.output/'gap_tables.jsonl').open('w',encoding='utf-8') as stream:
        for b in range(3,args.max_base+1):
            for a in range(2,b):
                row=record(a,b);records.append(row)
                stream.write(json.dumps(row,separators=(',',':'))+'\n')
    seconds=time.perf_counter()-started
    fields=['n','a','b','gcd','coprime','passes','sum_gaps','mandatory_comparisons','largest_gap','table_sha256']
    with (args.output/'gap_summary.csv').open('w',newline='',encoding='utf-8-sig') as stream:
        writer=csv.DictWriter(stream,fieldnames=fields);writer.writeheader()
        writer.writerows({k:r[k] for k in fields} for r in records)
    primary=[r for r in records if r['coprime']]
    duplicate_groups=defaultdict(list)
    for r in records:duplicate_groups[r['table_sha256']].append([r['a'],r['b']])
    duplicates=[v for v in duplicate_groups.values() if len(v)>1]
    examples=[record(a,b) for a,b in [(2,3),(11,12),(15,16),(21,22),(26,27),(100,101),(182,183),(400,2001)]]
    for k in (26,45):
        candidates=[r for r in primary if r['passes']==k]
        if candidates:
            examples.append(dict(min(candidates,key=lambda r:r['mandatory_comparisons']),
                                 selection=f'minimum compulsory scan among sampled {k}-pass tables'))
            examples.append(dict(max(candidates,key=lambda r:r['mandatory_comparisons']),
                                 selection=f'maximum compulsory scan among sampled {k}-pass tables'))
    result={
        'n':args.n,'sampling':'Complete unordered integer pairs 2 <= a < b <= max_base; coprime subset is primary.',
        'max_base':args.max_base,'source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),
        'generation_and_jsonl_seconds':seconds,
        'all_pairs':summarize(records),'coprime_pairs':summarize(primary),
        'noncoprime_pairs':summarize([r for r in records if not r['coprime']]),
        'coprime_max_base_sensitivity':{str(B):summarize([r for r in primary if r['b']<=B])
                                      for B in (20,40,60,100,args.max_base)},
        'duplicate_pair_count':len(records)-len(duplicate_groups),
        'duplicate_table_groups':duplicates,'examples':examples,
        'comparison_floor_definition':'V=sum_h(n-h); every executed ordinary insertion performs at least one key comparison.',
        'scope':'Gap generation and exact deterministic scan counts; no random sorting benchmark or optimality claim.',
    }
    (args.output/'length_distribution.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('duplicate_table_groups','examples')},ensure_ascii=False,indent=2))


if __name__=='__main__':
    main()
