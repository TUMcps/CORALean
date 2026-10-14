module

public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
public import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope

@[expose] public section

/-!
# `HybridDynamics/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {G P : ℕ → Type} {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================  `NonlinearReset.evaluate_toNonlinearReset`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- At every point, `evaluate` of `Transition.toNonlinearReset` is `Transition.reset`: the nonlinear
reset class contains the affine one, whatever the input. -/
theorem NonlinearReset.evaluate_toNonlinearReset (e : Transition G L 𝕋 n) (x : Vec ℝ n)
    (u : Vec ℝ 0) : e.toNonlinearReset.evaluate x u = e.reset x := rfl


-- ============================  `Transition.guard2polytope_reset`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The reset is untouched, so it is the same map. -/
theorem Transition.guard2polytope_reset (conv : G n → P n) (e : Transition G L 𝕋 n) :
    (e.guard2polytope conv).reset = e.reset := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
