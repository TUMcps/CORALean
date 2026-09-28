"""Deterministic binary64 inputs for comparing MATLAB, CORALean and exact arithmetic.

Writes inputs.json: every number as a 16-digit hex bit pattern (big-endian IEEE 754 binary64),
so all tools read bit-identical values.
"""
import json, random, struct

def hexf(x):
    return struct.pack('>d', x).hex()

rng = random.Random(20260928)
cases = {}
# sums and dot products of well-scaled random numbers
cases['v1e4'] = [rng.gauss(0, 1) for _ in range(10000)]
cases['w1e4'] = [rng.gauss(0, 1) for _ in range(10000)]
# ill-conditioned sum: large values that cancel, plus small ones
big = [rng.uniform(1e15, 1e16) * rng.choice((-1, 1)) for _ in range(500)]
cancel = []
for b in big:
    cancel += [b, -b * (1 + rng.uniform(-1e-12, 1e-12))]
cancel += [rng.uniform(-1, 1) for _ in range(1000)]
rng.shuffle(cancel)
cases['cancel'] = cancel
# matrices (row-major)
for n in (100, 500):
    cases[f'A{n}'] = [rng.gauss(0, 1) for _ in range(n * n)]
    cases[f'B{n}'] = [rng.gauss(0, 1) for _ in range(n * n)]

json.dump({k: [hexf(x) for x in v] for k, v in cases.items()}, open('inputs.json', 'w'))
print({k: len(v) for k, v in cases.items()})
