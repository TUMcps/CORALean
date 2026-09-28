"""Compares MATLAB's results with exact arithmetic and sequential IEEE round-to-nearest.

Exact values use Fraction; the sequential reference is Python float arithmetic, which is
IEEE 754 binary64 with rounding to nearest after every single operation (no fused multiply-add).
Optionally reads coralean_results.json (hardware nearest and IEEE .binary64 outward bounds).
"""
import json, math, os, random, struct, sys
from fractions import Fraction

def f(h):
    return struct.unpack('>d', bytes.fromhex(h))[0]

def ulps(a, b):
    """signed distance in units in the last place, via the ordered integer encoding"""
    def key(x):
        i = struct.unpack('>q', struct.pack('>d', x))[0]
        return i if i >= 0 else -(i & 0x7fffffffffffffff)
    return key(a) - key(b)

def nearest(q):
    """exact rational -> binary64, rounded to nearest (Python's Fraction->float is correctly rounded)"""
    return float(q)

inp = {k: [f(x) for x in v] for k, v in json.load(open('inputs.json')).items()}
mat = json.load(open('matlab_results.json'))
cl = json.load(open('coralean_results.json')) if os.path.exists('coralean_results.json') else None

def seqsum(x):
    s = 0.0
    for t in x:
        s = s + t
    return s

def seqdot(x, y):
    s = 0.0
    for a, b in zip(x, y):
        s = s + a * b
    return s

rows = []
def report(name, exact, seq, mb, ml, cl_key=None):
    ex_f = nearest(exact)
    r = {'op': name,
         'exact (rounded)': ex_f,
         'matlab builtin - exact [ulp]': ulps(mb, ex_f),
         'matlab loop == seq nearest': ml == seq,
         'seq nearest - exact [ulp]': ulps(seq, ex_f),
         'rel. diff builtin vs exact': float(abs(Fraction(mb) - exact) / abs(exact)) if exact != 0 else float('nan')}
    if cl is not None and cl_key in cl:
        c = cl[cl_key]
        hw, lo, hi = f(c['hardware_nearest']), f(c['ieee_down']), f(c['ieee_up'])
        r['hardware nearest == seq nearest'] = hw == seq
        r['IEEE [down,up] contains exact'] = Fraction(lo) <= exact <= Fraction(hi)
        r['IEEE [down,up] contains matlab builtin'] = lo <= mb <= hi
        r['IEEE width [ulp]'] = ulps(hi, lo)
    rows.append(r)

v, w, c = inp['v1e4'], inp['w1e4'], inp['cancel']
report('sum(v), n=1e4', sum(map(Fraction, v)), seqsum(v), f(mat['sum_v_builtin']), f(mat['sum_v_loop']), 'sum_v')
report('sum(cancel), n=2e3', sum(map(Fraction, c)), seqsum(c), f(mat['sum_cancel_builtin']), f(mat['sum_cancel_loop']), 'sum_cancel')
report("v'*w, n=1e4", sum(Fraction(a) * Fraction(b) for a, b in zip(v, w)), seqdot(v, w),
       f(mat['dot_vw_builtin']), f(mat['dot_vw_loop']), 'dot_vw')

rng = random.Random(1)
for n in (100, 500):
    A, B = inp[f'A{n}'], inp[f'B{n}']
    Cb = [f(h) for h in mat[f'mtimes{n}_builtin']]
    Cl = [f(h) for h in mat[f'mtimes{n}_loop']]
    idx = range(n * n) if n <= 100 else rng.sample(range(n * n), 2000)
    stats = {'entries': 0, 'builtin==exact_rounded': 0, 'builtin==seq': 0, 'loop==seq': 0,
             'max |builtin-exact| ulp': 0, 'max |seq-exact| ulp': 0, 'max rel diff builtin': 0.0}
    for e in idx:
        i, j = divmod(e, n)
        row = A[i * n:(i + 1) * n]
        col = B[j::n]
        ex = sum(Fraction(a) * Fraction(b) for a, b in zip(row, col))
        seq = seqdot(row, col)
        exf = nearest(ex)
        stats['entries'] += 1
        stats['builtin==exact_rounded'] += Cb[e] == exf
        stats['builtin==seq'] += Cb[e] == seq
        stats['loop==seq'] += Cl[e] == seq
        stats['max |builtin-exact| ulp'] = max(stats['max |builtin-exact| ulp'], abs(ulps(Cb[e], exf)))
        stats['max |seq-exact| ulp'] = max(stats['max |seq-exact| ulp'], abs(ulps(seq, exf)))
        if ex != 0:
            stats['max rel diff builtin'] = max(stats['max rel diff builtin'], float(abs(Fraction(Cb[e]) - ex) / abs(ex)))
    rows.append({'op': f'A*B, {n}x{n}', **stats})

print('MATLAB', mat['matlab_version'], '|', mat['blas'])
for r in rows:
    print(json.dumps(r))
json.dump(rows, open('comparison.json', 'w'), indent=1)

# ---------------------------------------------------------------------------
# opcompare verification: bit-identity of hardware_nearest against the sequential
# round-to-nearest reference above, interval containment (exact value, MATLAB's
# loop, MATLAB's builtin) for both the ieee_down/up and hardware_down/up bounds,
# and their widths in ulp. Written to coralean_summary.json, printed as a short
# table. Everything above this point is unchanged.
if cl is None:
    print()
    print('coralean_results.json not found -- skipping the opcompare verification')
else:
    def exact_sum(x):
        return sum(map(Fraction, x))

    def exact_dot(x, y):
        return sum(Fraction(a) * Fraction(b) for a, b in zip(x, y))

    def bounds(entry):
        return {k: f(entry[k]) for k in
                ('hardware_nearest', 'hardware_down', 'hardware_up', 'ieee_down', 'ieee_up')}

    summary = {}

    def verify_scalar(name, exact, seq, mb, ml):
        b = bounds(cl[name])
        summary[name] = {
            'bit_identical_to_seq_nearest': b['hardware_nearest'] == seq,
            'ieee_contains_exact': Fraction(b['ieee_down']) <= exact <= Fraction(b['ieee_up']),
            'ieee_contains_matlab_loop': b['ieee_down'] <= ml <= b['ieee_up'],
            'ieee_contains_matlab_builtin': b['ieee_down'] <= mb <= b['ieee_up'],
            'hardware_contains_exact':
                Fraction(b['hardware_down']) <= exact <= Fraction(b['hardware_up']),
            'hardware_contains_matlab_loop': b['hardware_down'] <= ml <= b['hardware_up'],
            'hardware_contains_matlab_builtin': b['hardware_down'] <= mb <= b['hardware_up'],
            'ieee_width_ulp': ulps(b['ieee_up'], b['ieee_down']),
            'hardware_width_ulp': ulps(b['hardware_up'], b['hardware_down']),
        }

    verify_scalar('sum_v', exact_sum(v), seqsum(v), f(mat['sum_v_builtin']), f(mat['sum_v_loop']))
    verify_scalar('sum_cancel', exact_sum(c), seqsum(c), f(mat['sum_cancel_builtin']),
                   f(mat['sum_cancel_loop']))
    verify_scalar('dot_vw', exact_dot(v, w), seqdot(v, w), f(mat['dot_vw_builtin']),
                   f(mat['dot_vw_loop']))

    def stats(ws):
        ws = sorted(ws)
        return {'min': ws[0], 'median': ws[len(ws) // 2], 'max': ws[-1]}

    def verify_matrix(name, n):
        A, B = inp[f'A{n}'], inp[f'B{n}']
        Cb = [f(h) for h in mat[f'mtimes{n}_builtin']]
        Cl = [f(h) for h in mat[f'mtimes{n}_loop']]
        cq = cl[name]
        hn = [f(h) for h in cq['hardware_nearest']]
        hd = [f(h) for h in cq['hardware_down']]
        hu = [f(h) for h in cq['hardware_up']]
        idn = [f(h) for h in cq['ieee_down']]
        idu = [f(h) for h in cq['ieee_up']]
        entries = n * n
        # cheap, float-only: exhaustive over every entry
        seqs = [seqdot(A[i * n:(i + 1) * n], B[j::n]) for i in range(n) for j in range(n)]
        bit_ident = sum(hn[e] == seqs[e] for e in range(entries))
        ieee_ml = sum(idn[e] <= Cl[e] <= idu[e] for e in range(entries))
        ieee_mb = sum(idn[e] <= Cb[e] <= idu[e] for e in range(entries))
        hw_ml = sum(hd[e] <= Cl[e] <= hu[e] for e in range(entries))
        hw_mb = sum(hd[e] <= Cb[e] <= hu[e] for e in range(entries))
        ieee_widths = [ulps(idu[e], idn[e]) for e in range(entries)]
        hw_widths = [ulps(hu[e], hd[e]) for e in range(entries)]
        # expensive, exact: every entry at n <= 100, else the same 2000-entry sample as above
        rng = random.Random(1)
        idx = list(range(entries)) if n <= 100 else rng.sample(range(entries), 2000)
        ieee_exact = 0
        hw_exact = 0
        for e in idx:
            i, j = divmod(e, n)
            ex = exact_dot(A[i * n:(i + 1) * n], B[j::n])
            ieee_exact += Fraction(idn[e]) <= ex <= Fraction(idu[e])
            hw_exact += Fraction(hd[e]) <= ex <= Fraction(hu[e])
        summary[name] = {
            'entries': entries,
            'bit_identical_to_seq_nearest': bit_ident,
            'ieee_contains_matlab_loop': ieee_ml,
            'ieee_contains_matlab_builtin': ieee_mb,
            'hardware_contains_matlab_loop': hw_ml,
            'hardware_contains_matlab_builtin': hw_mb,
            'exact_sample_size': len(idx),
            'ieee_contains_exact_sample': ieee_exact,
            'hardware_contains_exact_sample': hw_exact,
            'ieee_width_ulp': stats(ieee_widths),
            'hardware_width_ulp': stats(hw_widths),
        }

    verify_matrix('mtimes100', 100)
    verify_matrix('mtimes500', 500)

    json.dump(summary, open('coralean_summary.json', 'w'), indent=1)
    print()
    print('opcompare verification (coralean_results.json vs. exact/MATLAB)')
    for name, rec in summary.items():
        print(name, json.dumps(rec))
