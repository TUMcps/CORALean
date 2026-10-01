import CORALean.ContDynamics.LinearARX.LinearARX
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.Global.ExactScalar

/-!
# Conversion to a discrete-time linear system

The window `(y(k-p), …, y(k-1))` becomes the state, as in CORA's `nonlinearSysDT`,
`f(x,u) = [x(dim_y+1:end); f_ARX(x,u)]`: block `a < p-1` of the next window is
block `a+1` of this one, and the last block is `∑ Ā_i y(k-i)` — block `a'`
carries `Ā_{p-a'}`, `Fin.rev a'` here. The input terms `∑ B̄_i u(k-i+1)` are not
in `A`: they enter in state coordinates, through `inputMat` and `inputSet`.

CORA stacks the last `p+1` inputs into an input of dimension `dim_u (p+1)`;
`LinearSysDT` has no `B`, so those folds into the input set instead, which is what
loses the dependency between the copies of `u`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.toLinearSysDT (sys : LinearARX 𝕋 dy du p) : LinearSysDT 𝕋 (p * dy) where
  A := Matrix.of fun r c =>
    if (finProdFinEquiv.symm r).1.val + 1 < p then
      if (finProdFinEquiv.symm c).1.val = (finProdFinEquiv.symm r).1.val + 1
          ∧ (finProdFinEquiv.symm c).2 = (finProdFinEquiv.symm r).2 then 1 else 0
    else sys.Abar (Fin.rev (finProdFinEquiv.symm c).1)
      (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
