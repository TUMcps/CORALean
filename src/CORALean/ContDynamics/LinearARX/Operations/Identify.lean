module

public import CORALean.ContDynamics.LinearARX.Operations.IdentifyBlocks
public import CORALean.ContDynamics.LinearARX.Operations.IdentifyCandidate
public import CORALean.Global.DmdSelect

@[expose] public section

/-!
# `identify` of `LinearARX`, algorithm `dmd`

CORA's `identify` with `options.alg = 'dmd'` [1]: every rank `1, …, rankMax` gives a candidate
`[A B]`, and the one of least `computeError` is the system (`err`, compared by `lt`; both
arguments). The interpolation to a uniform step (`uniformTimeStepSize`) is not modelled, and
`'opt'` is a solver.

## Inputs
* `dt` – sampling time
* `lt` – order test on errors
* `err` – error of a candidate matrix
* `yNext` – successor outputs
* `V` – left singular vectors
* `s` – singular values
* `W` – right singular vectors

## Output
* the system of least error over all ranks, if any

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p N r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sys = linearARX.identify(traj)`, line by line of `priv_identifyDMD`. -/
noncomputable def LinearARX.identify (dt : ℝ) (lt : ℝ → ℝ → Bool)
    (err : Mat ℝ dy (p * dy + (p + 1) * du) → ℝ) (yNext : Fin N → Vec ℝ dy)
    (V : Mat ℝ (p * dy + (p + 1) * du) r) (s : Fin r → ℝ) (W : Mat ℝ N r) :
    Option (LinearARX ℝ dy du p) :=
  let Alist := LinearARX.identifyCandidate yNext V s W          -- Alist{rank}
  (dmdSelect lt err Alist r).map (LinearARX.identifyBlocks dt)     -- linearARX(A_, B_, dt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
