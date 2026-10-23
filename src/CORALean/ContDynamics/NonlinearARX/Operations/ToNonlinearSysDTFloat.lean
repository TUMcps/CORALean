module

public import CORALean.ContDynamics.NonlinearARX.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearARX.Operations.RevBlocks

@[expose] public section

/-!
# The conversion to a discrete-time system, on a float model

CORA's `nonlinearARX/nonlinearSysDT` [1] on the interval extension of `f_ARX`: block `a < p - 1`
of the next window is the box of block `a + 1` of this one, and the last block is the extension's
value, which reads the window and the inputs newest first, as the real conversion does. Only
existing bounds are moved, so no rounding enters beyond the extension's.

## Inputs
* `fm` – float model of the ARX system

## Output
* the float model of the converted discrete-time system

## References

* [1] `contDynamics/@nonlinearARX/nonlinearSysDT.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.FloatModel.toNonlinearSysDTFloat (fm : NonlinearARX.FloatModel 𝕋 dy du p) :
    NonlinearSysDT.FloatModel 𝕋 (p * dy) ((p + 1) * du) where
  f := fun X V =>
    -- the window and the inputs, newest first, as `f_ARX` reads them
    let Y := fm.f
      ⟨fun s => X.inf (NonlinearARX.revBlocks s),
       fun s => X.sup (NonlinearARX.revBlocks s)⟩
      ⟨fun s => V.inf (NonlinearARX.revBlocks s),
       fun s => V.sup (NonlinearARX.revBlocks s)⟩
    ⟨fun r => if h : (finProdFinEquiv.symm r).1.val + 1 < p then
        X.inf (finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, h⟩ : Fin p),
          (finProdFinEquiv.symm r).2))
      else Y.inf (finProdFinEquiv.symm r).2,
     fun r => if h : (finProdFinEquiv.symm r).1.val + 1 < p then
        X.sup (finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, h⟩ : Fin p),
          (finProdFinEquiv.symm r).2))
      else Y.sup (finProdFinEquiv.symm r).2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
