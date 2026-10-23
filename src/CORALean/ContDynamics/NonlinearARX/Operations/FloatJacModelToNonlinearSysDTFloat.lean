module

public import CORALean.ContDynamics.NonlinearARX.Definitions.FloatJacModel
public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatJacModel
public import CORALean.ContDynamics.NonlinearARX.Operations.RevBlocks

@[expose] public section

/-!
# The conversion to a discrete-time system, on a float model with Jacobians

CORA's `nonlinearARX/computeGO` [1] assembles the converted system's Jacobians from those of
`f_ARX`: `A_tilde = [A_tilde_firstRows; A_lin]` and `B_tilde = [B_tilde_firstRows; B_lin]`, the
first rows the shift of the window (an identity block, and zeros in the inputs) and the last
block row the Jacobians of `f_ARX`, read newest first as the conversion does. The value is
`FloatModel.toNonlinearSysDTFloat`'s. Only stored bounds and exact `one`/`zero` are placed, so no
rounding enters beyond the extensions'.

## Inputs
* `fm` – float Jacobian model of the ARX system

## Output
* the float Jacobian model of the converted discrete-time system

## References

* [1] `contDynamics/@nonlinearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.FloatJacModel.toNonlinearSysDTFloat
    (fm : NonlinearARX.FloatJacModel 𝕋 dy du p) :
    NonlinearSysDT.FloatJacModel 𝕋 (p * dy) ((p + 1) * du) (p * dy) where
  f := (NonlinearARX.FloatModel.toNonlinearSysDTFloat ⟨fm.f⟩).f
  jacX := fun X V =>
    -- the window and the inputs, newest first, as `f_ARX` reads them
    let Y : Interval (Vec 𝕋 (p * dy)) :=
      ⟨fun s => X.inf (NonlinearARX.revBlocks s),
       fun s => X.sup (NonlinearARX.revBlocks s)⟩
    let W : Interval (Vec 𝕋 ((p + 1) * du)) :=
      ⟨fun s => V.inf (NonlinearARX.revBlocks s),
       fun s => V.sup (NonlinearARX.revBlocks s)⟩
    let A_lin := fm.jacY Y W                                         -- A_lin
    -- A_tilde = [A_tilde_firstRows; A_lin]
    ⟨fun r c => if h : (finProdFinEquiv.symm r).1.val + 1 < p then
        (if c = finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, h⟩ : Fin p),
          (finProdFinEquiv.symm r).2) then one else zero)
      else A_lin.inf (finProdFinEquiv.symm r).2
        (NonlinearARX.revBlocks c),
     fun r c => if h : (finProdFinEquiv.symm r).1.val + 1 < p then
        (if c = finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, h⟩ : Fin p),
          (finProdFinEquiv.symm r).2) then one else zero)
      else A_lin.sup (finProdFinEquiv.symm r).2
        (NonlinearARX.revBlocks c)⟩
  jacU := fun X V =>
    -- the window and the inputs, newest first, as `f_ARX` reads them
    let Y : Interval (Vec 𝕋 (p * dy)) :=
      ⟨fun s => X.inf (NonlinearARX.revBlocks s),
       fun s => X.sup (NonlinearARX.revBlocks s)⟩
    let W : Interval (Vec 𝕋 ((p + 1) * du)) :=
      ⟨fun s => V.inf (NonlinearARX.revBlocks s),
       fun s => V.sup (NonlinearARX.revBlocks s)⟩
    let B_lin := fm.jacU Y W                                         -- B_lin
    -- B_tilde = [B_tilde_firstRows; B_lin]
    ⟨fun r c => if (finProdFinEquiv.symm r).1.val + 1 < p then zero
      else B_lin.inf (finProdFinEquiv.symm r).2
        (NonlinearARX.revBlocks c),
     fun r c => if (finProdFinEquiv.symm r).1.val + 1 < p then zero
      else B_lin.sup (finProdFinEquiv.symm r).2
        (NonlinearARX.revBlocks c)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
