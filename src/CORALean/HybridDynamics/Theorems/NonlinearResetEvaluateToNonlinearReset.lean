module

public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
public import CORALean.HybridDynamics.Operations.TransitionToNonlinearReset

@[expose] public section

/-!
# The nonlinear reset of a transition evaluates to the transition's reset

At every point, `evaluate` of `Transition.toNonlinearReset` is `Transition.reset`: the nonlinear
reset class contains the affine one, whatever the input.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.evaluate_toNonlinearReset (e : Transition G L 𝕋 n) (x : Vec ℝ n)
    (u : Vec ℝ 0) : e.toNonlinearReset.evaluate x u = e.reset x := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
