import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
import CORALean.ContSet.Zonotope.Float.Operations.CartProd
import CORALean.ContSet.Zonotope.Float.Operations.Project

/-!
# Parametric nonlinear reachability in floats

`NonlinParamSys.WithSteps.reachUnion` lifts the parameter `p ∈ P` to the last `q` coordinates of
the state with zero dynamics (`augment`) and reads the run of `NonlinearSys` off its first `n`
coordinates. Here the same lift is run in `𝕋`: the initial set is the float product `X₀ × P`
(`Zonotope.cartProd`), the run is `NonlinearSys.FloatModel.reachFloat` of a `FloatModel` of the
lifted field, and each window is projected back (`Zonotope.project`). Soundness is
`NonlinParamSys.reachFloat_outer`, against every constant-parameter run.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows of the lifted run from `X₀ × P`, each projected to the first `n` coordinates; the
`FloatModel` is one of `sys.augment`. -/
def NonlinParamSys.reachFloat (_sys : NonlinParamSys n m q)
    (fm : NonlinearSys.FloatModel 𝕋 (n + q) m) (P : Zonotope (Vec 𝕋 q))
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) :=
  let Z₀ := params.R0.cartProd P                                    -- X₀ × P
  (fm.reachFloat ⟨Z₀, params.U, params.tStart, params.tFinal⟩ options).map fun Rs =>
    Rs.map fun R => R.project (Fin.castAdd q)                       -- back to the state

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
