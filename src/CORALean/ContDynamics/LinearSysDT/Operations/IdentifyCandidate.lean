module

public import CORALean.Global.DmdCandidate
public import CORALean.Global.DmdRegressor
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The DMD candidate of rank `k` of `LinearSysDT.identify`

`[A c B]` with `x(k+1) = A x + B u + c`: the regressors `[x; 1; u]` of the data points are
the columns of `X1`, their `xNext` those of `X2`, and the candidate is `X2 W_k S_k⁻¹ V_kᵀ`
for an economy SVD `X1 = V S Wᵀ`, which is an argument.
The source is [1].

## Inputs
* `xNext` – successor states
* `V` – left singular vectors
* `s` – singular values
* `W` – right singular vectors
* `k` – rank

## Output
* the candidate matrix of rank `k`

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One data point per `j : Fin N`, its `xNext` here; the state and input are in the SVD. -/
noncomputable def LinearSysDT.identifyCandidate (xNext : Fin N → Vec ℝ n)
    (V : Mat ℝ (n + 1 + m) r) (s : Fin r → ℝ) (W : Mat ℝ N r) (k : ℕ) :
    Mat ℝ n (n + 1 + m) :=
  let X2 : Mat ℝ n N := Matrix.of fun i j => xNext j i          -- the successors
  dmdCandidate X2 V s W k                                  -- X2 * W_k * diag(1./S_k) * V_k'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
