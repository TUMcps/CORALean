import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
import CORALean.ContDynamics.NonlinearSysDT.Operations.IdentifyCandidate
import CORALean.Global.DmdSelect

/-!
# `identify` of `NonlinearSysDT`, algorithm `dmd`

CORA's `identify` with `options.alg = 'dmd'` [1]: every rank `1, …, rankMax` gives a candidate
system `f(x,u) = A φ(x,u)`, and the one of least `computeError` is the result (`err`, compared by
`lt`; both arguments, as `φ`). The data points are the SVD of their basis values and the
xNext; the interpolation to a uniform step and the finite differences of `getDataPoints`
are not modelled. `'opt'`, `'sparse'` and `'nested'` are not formalized.

## References

* [1] `contDynamics/@nonlinearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m N r d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sys = identify(traj)`, line by line of `priv_identifyDMD`. -/
noncomputable def NonlinearSysDT.identify (φ : Vec ℝ n → Vec ℝ m → Vec ℝ d) (lt : ℝ → ℝ → Bool)
    (err : NonlinearSysDT n m → ℝ) (xNext : Fin N → Vec ℝ n) (V : Mat ℝ d r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) : Option (NonlinearSysDT n m) :=
  let Alist := NonlinearSysDT.identifyCandidate xNext V s W               -- Alist{rank}
  let sysTmp := fun k =>                                           -- sysTmp
    (NonlinearSysDT.mk fun x u => Alist k *ᵥ φ x u : NonlinearSysDT n m)
  dmdSelect lt err sysTmp r                                       -- best rank

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
