import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
import CORALean.HybridDynamics.Operations.TransitionToNonlinearReset

/-!
# The nonlinear reset of a transition evaluates to the transition's reset

At every point, `evaluate` of `Transition.toNonlinearReset` is `Transition.reset`: the nonlinear
reset class contains the affine one, whatever the input.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.evaluate_toNonlinearReset (e : Transition G L 𝕋 n) (x : Vec ℝ n)
    (u : Vec ℝ 0) : e.toNonlinearReset.evaluate x u = e.reset x := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
