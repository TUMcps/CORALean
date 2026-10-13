import CORALean.ContDynamics.LinearSys.Definitions.ReachInner
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# The inner approximation, at a representation

`timePointStepInner` is one step of `reachInner`. Chaining needs the error as
a set that `e^{AΔt}` can carry, and a ball does not stay a ball under a
matrix; its box, `timePointStepErrorBox`, stays a zonotope. That is what
gives `reachInnerRep`: `minkDiffRep` of the run by its error, at a generator
representation `M` the caller offers and the operation checks. A wrong `M`
gives `none`, costing precision and never soundness.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same difference at a representation, `none` where the caller's
generator representation `M` does not check out. -/
noncomputable def LinearSys.reachInnerRep (sys : LinearSys 𝕋 n) (Δt : ℝ) (η o : ℕ)
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin ((sys.discretize Δt).reach (S := 𝒵) ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩
      ⟨o, ho⟩).h → Fin (sys.reachError Δt η o ho R₀ U k).h → ℝ) : Option (Zonotope (Vec ℝ n)) :=
  ((sys.discretize Δt).reach (S := 𝒵) ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩
    ⟨o, ho⟩).minkDiffRep
    (sys.reachError Δt η o ho R₀ U k) M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
