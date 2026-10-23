module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
public import CORALean.ContDynamics.NonlinearARX.Operations.RevBlocks

@[expose] public section

/-!
# Conversion to a discrete-time nonlinear system

CORA's `nonlinearARX/nonlinearSysDT` [1]: a state of `dim_y · p`, the window `(y(k-p), …, y(k-1))`
of the last `p` outputs, and an input of `dim_u · (p+1)`, the inputs `(u(k-p), …, u(k))`, both
oldest first, `f(x,u) = [x(dim_y+1:end); f_ARX(x,u)]`: block `a < p-1` of the next window is block
`a+1` of this one, and the last block is `f_ARX`; the output is CORA's default, the state. Here `f`
reads its arguments newest first, as the class documents, so the window and the input are reversed
block-wise (`Fin.rev`) on the way in. `feed u k` is the input signal that results: block `a` holds
`u(k+a)`. Unlike `LinearARX`, nothing folds into an input set: `NonlinearSysDT` has an input of
dimension `dim_u (p+1)`, which keeps the dependency between the copies of `u`.

## Inputs
* `sys` – ARX system

## Output
* the discrete-time nonlinear system on the output window

## References

* [1] `contDynamics/@nonlinearARX/nonlinearSysDT.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.toNonlinearSysDT (sys : NonlinearARX dy du p) :
    NonlinearSysDT (p * dy) ((p + 1) * du) where
  f x v := fun r =>
    if h : (finProdFinEquiv.symm r).1.val + 1 < p then
      x (finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, h⟩ : Fin p),
        (finProdFinEquiv.symm r).2))
    else
      sys.f (fun s => x (NonlinearARX.revBlocks s))
        (fun s => v (NonlinearARX.revBlocks s)) (finProdFinEquiv.symm r).2
  q := p * dy
  g x _ := x
  dt := sys.dt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
