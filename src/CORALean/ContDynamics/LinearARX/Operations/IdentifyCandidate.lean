module

public import CORALean.ContDynamics.LinearARX.Operations.IdentifyRegressor
public import CORALean.Global.DmdCandidate

@[expose] public section

/-!
# The DMD candidate of rank `k` of `LinearARX.identify`

`[A B]` with `y(j) = ∑ A_i y(j-i) + ∑ B_j u(j-j)`: the regressors of the data points are the
columns of `X1`, their `y(j)` those of `X2`, and the candidate is `X2 W_k S_k⁻¹ V_kᵀ`
(`aux_dynamicModeDecomposition`) for an economy SVD `X1 = V S Wᵀ`, which is an argument.
The source is [1].

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p N r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One data point per `j : Fin N`, its successor output `yNext j` here; the rest is in the SVD. -/
noncomputable def LinearARX.identifyCandidate (yNext : Fin N → Vec ℝ dy)
    (V : Mat ℝ (p * dy + (p + 1) * du) r) (s : Fin r → ℝ) (W : Mat ℝ N r) (k : ℕ) :
    Mat ℝ dy (p * dy + (p + 1) * du) :=
  let X2 : Mat ℝ dy N := Matrix.of fun i j => yNext j i          -- points.xNext
  dmdCandidate X2 V s W k                                  -- X2*W_*diag(1./diag(S_))*V_'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
