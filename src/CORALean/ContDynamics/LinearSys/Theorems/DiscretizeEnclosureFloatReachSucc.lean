module

public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInputFloat
public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach

@[expose] public section

/-!
# One step of the float sampled run

`discretizeEnclosureFloat`'s `reach`, with `inputSolutionFloat` as its input set,
takes a step as `timePointStepInputFloat` from the previous set, then reduces:
`reach`'s own recursion, read past the instances' `materialise`. What lets a
proof about the run work with the step's named operations.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of the float sampled run is the float step from the previous set, reduced. -/
theorem LinearSys.discretizeEnclosureFloat_reach_succ (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ)
    {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) :
    (sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k + 1⟩ ⟨o, ho⟩
      = (sys.timePointStepInputFloat Δt η
          ((sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
            ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩) U).reduce o := by
  show Reduce.reduce (sys.timePointStepInputFloat Δt η ((sys.discretizeEnclosureFloat Δt η).reach
    (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩) U) o = _
  exact Zonotope.materialise_eq _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
