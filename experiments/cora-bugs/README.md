# CORA bug witnesses run in MATLAB

Each `cora-issue` note of `references/coverage/` (one per entry of `experiments/paper/cora-bugs.json`)
ends with a line `MATLAB R2024b, CORA v2026.1.0 (904a444): <observed output>`. This directory holds
the scripts that produced it and the record.

* `R.m` — the harness: `R(id, code)` evaluates the MATLAB statements `code` (which set `out`), catches
  an error and prints `RES|id|output`.
* `runs/run01.m` … `runs/run17.m` — the batches, in the order they were run, errors of the invocation
  included (a batch that failed because of a wrong call was repeated in a later one). Run one with
  `matlab -batch "run('experiments/cora-bugs/runs/run01.m')" | grep '^RES'`; CORA must be on the path
  (`installCORA`). `em/encloseMany.m` and `em/filterOut.m` are copies of the zonotope methods, which MATLAB cannot dispatch
  on a cell; `em/priv_zonotopeContainment_ellipsoidSamplingDual.m` is the private function with its
  one undefined variable repaired (`Z2` to `Z`, l. 86), to see what it computes once it runs. `run16.m`
  re-runs the eight rows the first batches did not reproduce, at the entry points that reach their
  code; all eight are `confirmed` now, five of them with a different claim than the note first made.
* `runs/run18.m` — `neuralNetwork/verify` (`'zonotack'`) on random 2-input ReLU networks of CORA.cpp's
  witness search, run four times (`repair = {}`, then `{'dummy'}`, `{'stale'}`, `{'center'}`).
  `nn/witnessNets.py SEED...` writes `nn/witnessNet.m` (weights, the bound `t` of the unsafe set,
  a sampled unsafe input), `nn/runWitness.m` runs one network, `nn/patchVerify.m` applies one of
  CORA.cpp's repairs to a temporary copy of `@neuralNetwork`, and `nn/CHECKS_ENABLED.m` shadows CORA's
  macro to `false`.
* `runs/run19.m` — `@nnActivationLayer/evaluateZonotopeBatch` under an interval center: a one-layer
  example whose output set misses the image of `x = 0`, then `verify` on networks 7, 25, 43
  (`'v2-input'`) and 5, 40, 53 (`'v2'`), run with `repair = {}`, `{'offset'}` and
  `{'dummy', 'stale', 'center', 'offset'}`. `nn/patchOffset.m` puts a copy of `@nnActivationLayer`
  first on the path whose `notdDimsIdx` is taken before `dDimsIdx` is cut to its first `dn` rows.
* `results.tsv` — the record: coverage row, status (`confirmed`, `partly confirmed`, `not reproduced`,
  `not run`) and the observed output, as written into the notes. The status is also the `matlab` field
  of `cora-bugs.json`.

A row is `not run` when no concrete input exists in the note or the witness was not constructed; the
output is then a reason. `not reproduced` means MATLAB did something other than the note claims (the
note says what). The MATLAB runs used SDPT3 (YALMIP), not MOSEK or SeDuMi: `sedumi` is not installed here.
