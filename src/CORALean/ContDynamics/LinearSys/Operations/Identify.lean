module

public import CORALean.ContDynamics.LinearSys.Operations.IdentifyCandidate
public import CORALean.ContDynamics.LinearSys.Operations.OfABc
public import CORALean.Global.DmdBlocks
public import CORALean.Global.DmdSelect

@[expose] public section

/-!
# `identify` of `LinearSys`, algorithm `dmd`

CORA's `identify` with `options.alg = 'dmd'` [1]: every rank `1, …, rankMax` gives a
candidate `[A c B]`, and the one of least `computeError` is the system (`err`, compared by
`lt`; both arguments). The data points are the SVD of their regressors `[x; 1; u]` and
the `dx`; the interpolation to a uniform step (`uniformTimeStepSize`) and the finite
differences of `getDataPoints` are not modelled. Returns the system CORA's constructor builds,
`ofABc`, the remaining matrices at their defaults. `'opt'` is `fmincon`.

## Inputs
* `lt` – strict comparison oracle on reals
* `err` – error measure of a candidate
* `dx` – state derivative data
* `V` – singular vectors over the state-input space
* `s` – singular values
* `W` – singular vectors over the data points

## Output
* identified system, if a candidate passes the error test

## References

* [1] `contDynamics/@linearSys/private/priv_identifyDMD.m`
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
noncomputable def LinearSys.identify (lt : ℝ → ℝ → Bool) (err : Mat ℝ n (n + 1 + m) → ℝ)
    (dx : Fin N → Vec ℝ n) (V : Mat ℝ (n + 1 + m) r)
    (s : Fin r → ℝ) (W : Mat ℝ N r) : Option (LinearSys ℝ n) :=
  let Alist := LinearSys.identifyCandidate dx V s W        -- Alist{rank}
  (dmdSelect lt err Alist r).map fun M =>                          -- best rank
    let (A, B, c) := dmdBlocks M                                   -- A, B, c
    LinearSys.ofABc A B c                                          -- linearSys(A, B, c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
