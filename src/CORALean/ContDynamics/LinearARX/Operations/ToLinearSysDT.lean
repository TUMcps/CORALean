module

public import CORALean.ContDynamics.LinearARX.LinearARX
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
public import CORALean.Global.ExactScalar

@[expose] public section

/-!
# Conversion to a discrete-time linear system

The window `(y(k-p), …, y(k-1))` becomes the state, as in CORA's `nonlinearSysDT`,
`f(x,u) = [x(dim_y+1:end); f_ARX(x,u)]`: block `a < p-1` of the next window is block `a+1` of
this one, and the last block is `∑ Ā_i y(k-i)`, block `a'` carrying `Ā_{p-a'}`. The input terms
`∑ B̄_i u(k-i+1)` enter in state coordinates, through `inputMat` and `inputSet`. CORA stacks the
last `p+1` inputs into an input of dimension `dim_u (p+1)`; the converted system is the canonical
form `LinearSysDT.canonical`, so they fold into the input set, which loses the dependency
between the copies of `u`.

## Inputs
* `sys` – ARX system

## Output
* the discrete-time system on the output window
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.toLinearSysDT (sys : LinearARX 𝕋 dy du p) : LinearSysDT 𝕋 (p * dy) :=
  LinearSysDT.canonical (Matrix.of fun r c =>
    if (finProdFinEquiv.symm r).1.val + 1 < p then
      if (finProdFinEquiv.symm c).1.val = (finProdFinEquiv.symm r).1.val + 1
          ∧ (finProdFinEquiv.symm c).2 = (finProdFinEquiv.symm r).2 then 1 else 0
    else sys.Abar (Fin.rev (finProdFinEquiv.symm c).1)
      (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2) sys.dt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
