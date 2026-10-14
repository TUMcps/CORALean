module

public import CORALean.ContDynamics.LinearSysDT.Operations.IdentifyCandidate
public import CORALean.Global.DmdBlocks
public import CORALean.Global.DmdSelect

@[expose] public section

/-!
# `identify` of `LinearSysDT`, algorithm `dmd`

CORA's `identify` with `options.alg = 'dmd'` [1]: every rank `1, …, rankMax` gives a
candidate `[A c B]`, and the one of least `computeError` is the system (`err`, compared by
`lt`; both arguments). The data points are the SVD of their regressors `[x; 1; u]` and
the `xNext`; the interpolation to a uniform step (`uniformTimeStepSize`) and the finite
differences of `getDataPoints` are not modelled. Returns the triple `(A, B, c)` CORA hands its
constructor, the remaining matrices being its defaults. `'opt'` is `fmincon`.

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sys = identify(traj)`, line by line of `priv_identifyDMD`. -/
noncomputable def LinearSysDT.identify (lt : ℝ → ℝ → Bool) (err : Mat ℝ n (n + 1 + m) → ℝ)
    (xNext : Fin N → Vec ℝ n) (V : Mat ℝ (n + 1 + m) r)
    (s : Fin r → ℝ) (W : Mat ℝ N r) : Option (Mat ℝ n n × Mat ℝ n m × Vec ℝ n) :=
  let Alist := LinearSysDT.identifyCandidate xNext V s W        -- Alist{rank}
  (dmdSelect lt err Alist r).map dmdBlocks                         -- best rank, A, B, c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
