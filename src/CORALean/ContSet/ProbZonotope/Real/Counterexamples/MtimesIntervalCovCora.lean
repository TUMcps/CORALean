module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `ProbZonotope.mtimesIntervalCovCora`: the covariance after `interval * probZonotope`

`@probZonotope/mtimes.m` (l. 53-68) maps a numeric matrix through `Z` and `cov`, but an interval
matrix through `Z` and `g` only:

```
if isnumeric(matrix)     probZ.Z = matrix*probZ.Z;  probZ.cov = matrix*probZ.cov*matrix';
elseif isa(matrix,'interval')
    probZ.Z = [T*probZ.Z, diag(S*Zsum)];  probZ.g = T*probZ.g;      % cov is not touched
```

The constructor sets `gauss = true` and `cov = sigma(obj)`, and `probReduce` (called by `sigma`,
`zonotope(probZ,m)`, `interval`) takes `newSigma = cov` when `gauss == 1` and ignores `g`. One
dimension, the interval matrix a point `T` (`S = 0`): the state is `g`, `cov` and `gauss`, `sigma`
reads `cov` or `g * g`. Read from the source, not run.

# CORA's `sigma(interval(2*eye(2)) * probZ)` is the unmapped covariance

`probZonotope([0;0], eye(2))` has `cov = I`, `g = I`. `interval(2*eye(2)) * probZ` sets `g = 2I`
and leaves `cov`, so `sigma` returns `I` and `zonotope(R, 2)` has generators `2I`, where the map
`x ↦ 2x` gives `sigma = 4I`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `sigma` is `1` for the map `x ↦ 2x`, whose covariance is `4`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The probabilistic part of a `probZonotope` in one dimension: the generator `g`, the cached
covariance `cov` and the flag `gauss`. -/
structure ProbZonotope.CovStateCora where
  g : ℝ
  cov : ℝ
  gauss : Bool

/-- CORA's `interval * probZ` for a point interval `T`: `probZ.g = T*probZ.g`, `cov` kept. -/
def ProbZonotope.mtimesIntervalCovCora (T : ℝ) (s : ProbZonotope.CovStateCora) :
    ProbZonotope.CovStateCora :=
  { s with g := T * s.g }

/-- CORA's `sigma(probZ)` (through `probReduce`): `cov` if `gauss`, else `g * g'`. -/
def ProbZonotope.sigmaCovCora (s : ProbZonotope.CovStateCora) : ℝ :=
  if s.gauss = true then s.cov else s.g * s.g


-- =======================================  MAIN THEOREM  ======================================= --

/-- For the state of `probZonotope([0], 1)` (`g = 1`, `cov = 1`, `gauss`) and `T = 2` CORA's
`sigma` is `1`; the map `x ↦ 2x` has covariance `2 * 1 * 2 = 4`, which is what the numeric branch
computes. -/
theorem ProbZonotope.mtimesIntervalCov_cora_counterexample :
    ProbZonotope.sigmaCovCora
        (ProbZonotope.mtimesIntervalCovCora 2 ⟨1, 1, true⟩) = 1 ∧
      (1 : ℝ) ≠ 2 * 1 * 2 := by
  refine ⟨?_, by norm_num⟩
  simp [ProbZonotope.sigmaCovCora, ProbZonotope.mtimesIntervalCovCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
