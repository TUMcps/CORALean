import CORALean.ContDynamics.NonlinearSys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinDASys.Operations.ToNonlinearSys

/-!
# Differential-algebraic reachability in floats

As at the real layer (`NonlinDASys.WithSteps.reachUnion`), the algebraic variable is eliminated
through a supplied `ReducedModel` and the ordinary system it leaves is run. Here that run is
`NonlinearSys.FloatModel.reachFloat`, from a `FloatModel` of the reduced field
`x ↦ f(x, h(x, u), u)`. CORA's linearization of the DAE with an algebraic error term is not what
is run. Soundness is `NonlinDASys.reachFloat_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows of the reduced ordinary system's float run; `fm` is a float model of
`red.toNonlinearSys`. -/
def NonlinDASys.reachFloat {sys : NonlinDASys n p m} (_red : sys.ReducedModel)
    (fm : NonlinearSys.FloatModel 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) :=
  fm.reachFloat params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
