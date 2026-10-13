module

public import CORALean.ContDynamics.NonlinearARX.Operations.Feed
public import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# `NonlinearARX.computeGO`

CORA's `nonlinearARX/computeGO` [1] with `compute_params = true`, `x0` a point: the output-error
linearization of the converted system `toNonlinearSysDT` along the reference run, with the
selection matrix `outputSel` as the output equation (`C_tilde`, no feedthrough) and the stacked
reference inputs `feed p u_ref` (`getStackedU`). It is `NonlinearSysDT.computeGO` of that
system, whose products `A_tilde{k} ... A_tilde{k-j}` are the recursion
`A_k{j+1} = A_k{j} A_tilde{k-j}`.
Step `k` here is the window `stack y k`, CORA's step `k + p`; the first `p` outputs are the
window `x0` itself and need no linearization, which is CORA's `C{k}`, `D{k,·}` for `k ≤ n_p`.

## References

* [1] `contDynamics/@nonlinearARX/computeGO.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters along the reference run from the window `x0` under `u_ref`. -/
noncomputable def NonlinearARX.computeGO (sys : NonlinearARX dy du p) (x0 : Vec ℝ (p * dy))
    (u_ref : ℕ → Vec ℝ du) : NonlinearSysDT.GO (p * dy) ((p + 1) * du) dy :=
  let nlnsysDT := sys.toNonlinearSysDT                             -- nlnARX.nonlinearSysDT
  let u_stacked := NonlinearARX.feed p u_ref                       -- getStackedU(nlnARX,u_ref)
  let C_tilde := sys.outputSel (𝕋 := ℝ)                            -- C_tilde
  nlnsysDT.computeGO (fun x _ => C_tilde *ᵥ x) x0 u_stacked        -- y_d(k) = C_tilde x_d(k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
