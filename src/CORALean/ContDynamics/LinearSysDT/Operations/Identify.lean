module

public import CORALean.ContDynamics.LinearSysDT.Operations.IdentifyCandidate
public import CORALean.ContDynamics.LinearSysDT.Operations.OfABc
public import CORALean.Global.DmdBlocks
public import CORALean.Global.DmdSelect

@[expose] public section

/-!
# `identify` of `LinearSysDT`, algorithm `dmd`

CORA's `identify` with `options.alg = 'dmd'` [1]: every rank `1, …, rankMax` gives a
candidate `[A c B]`, and the one of least `computeError` is the system (`err`, compared by
`lt`; both arguments). The data points are the SVD of their regressors `[x; 1; u]` and
the `xNext`; the interpolation to a uniform step (`uniformTimeStepSize`) and the finite
differences of `getDataPoints` are not modelled. Returns the system CORA's constructor builds,
`ofABc`, the remaining matrices at their defaults, at the data's sampling time `dt`.
`'opt'` is `fmincon`.

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
noncomputable def LinearSysDT.identify (dt : ℝ) (lt : ℝ → ℝ → Bool)
    (err : Mat ℝ n (n + 1 + m) → ℝ)
    (xNext : Fin N → Vec ℝ n) (V : Mat ℝ (n + 1 + m) r)
    (s : Fin r → ℝ) (W : Mat ℝ N r) : Option (LinearSysDT ℝ n) :=
  let Alist := LinearSysDT.identifyCandidate xNext V s W        -- Alist{rank}
  (dmdSelect lt err Alist r).map fun M =>                          -- best rank
    let (A, B, c) := dmdBlocks M                                   -- A, B, c
    LinearSysDT.ofABc A B c dt                                     -- linearSysDT(A, B, c, dt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
