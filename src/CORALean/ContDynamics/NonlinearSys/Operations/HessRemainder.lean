import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.NormMag
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.Global.Float.BilinUp

/-!
# The abstraction error from a Hessian enclosure

CORA's `priv_abstrerr_lin` at `tensorOrder = 2`, in `𝕋`: with `dz`
bounding `|z - z✱|` over `X × U` and `H_` the entrywise magnitude of the Hessian
box there, the second-order remainder lies in `[-l, l]`, `lᵢ = 0.5 * dz' * H_ᵢ * dz`.

`A` and `B` are the centres the float run linearizes with, not the Jacobian
itself, so the first-order slack `([J(z✱)] - A)(X - x✱) ⊕ ([J_u(z✱)] - B)(U - u✱)`
is added, with the Jacobian box taken at the point and so as thin as the model
makes it. This is the box `slopeRemainder` replaces when no Hessian is known:
second order in the deviation from `z✱` where that one is first.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `([J_x(z✱)] - A)(X - x✱) ⊕ ([J_u(z✱)] - B)(U - u✱) ⊕ [-l, l]`, `lᵢ = ½ dzᵀ |Hᵢ| dz`,
the Hessian box taken over `X × U`. -/
def NonlinearSys.FloatHessModel.hessRemainder (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 n) :=
  let Jx := fm.jacX (Interval.point xs) (Interval.point us)          -- [∂f/∂x (z✱)]
  let Ju := fm.jacU (Interval.point xs) (Interval.point us)          -- [∂f/∂u (z✱)]
  let ΔJx := Interval.matPlus Jx (Interval.point fun i j => neg (A i j))  -- [∂f/∂x (z✱)] - A
  let ΔJu := Interval.matPlus Ju (Interval.point fun i j => neg (B i j))  -- [∂f/∂u (z✱)] - B
  let IHx := Interval.plus X (Interval.point fun i => neg (xs i))   -- IHx = X - x✱
  let IHu := Interval.plus U (Interval.point fun i => neg (us i))   -- IHu = U - u✱
  let dz : Vec 𝕋 (n + m) := Fin.append IHx.normMag IHu.normMag       -- dz = [dx; du]
  let H := fm.hess X U                                              -- H = hessian(totalInt)
  let Habs := fun i j k => maximum (absolute ((H i).inf j k)) (absolute ((H i).sup j k))
  let l : Vec 𝕋 n := fun i => half (bilinUp dz (Habs i) dz)          -- 0.5 * dz' * H_ * dz
  Interval.plus (Interval.plus (Interval.mtimesIntervalMat ΔJx IHx)
    (Interval.mtimesIntervalMat ΔJu IHu)) ⟨fun i => neg (l i), l⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
