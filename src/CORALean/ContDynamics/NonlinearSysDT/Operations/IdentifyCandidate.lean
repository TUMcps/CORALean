module

public import CORALean.Global.DmdCandidate
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The DMD candidate of rank `k` of `NonlinearSysDT.identify`

`A` with `x(k+1) = A φ(x, u)` for a basis `φ`: the regressors `φ(x, u)` of the data points are the
columns of `X1`, their `xNext` those of `X2`, and the candidate is `X2 W_k S_k⁻¹ V_kᵀ` for an
economy SVD `X1 = V S Wᵀ`, which is an argument, as is `φ` (CORA's `'trig'`, `'quad'`, ... bases
or `options.phi`). The source is [1].

## References

* [1] `contDynamics/@nonlinearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N r d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One data point per `j : Fin N`, its xNext here; the basis values are in the SVD. -/
noncomputable def NonlinearSysDT.identifyCandidate (xNext : Fin N → Vec ℝ n)
    (V : Mat ℝ d r) (s : Fin r → ℝ) (W : Mat ℝ N r) (k : ℕ) : Mat ℝ n d :=
  let X2 : Mat ℝ n N := Matrix.of fun i j => xNext j i          -- the targets
  dmdCandidate X2 V s W k                                  -- X2 * W_k * diag(1./S_k) * V_k'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
