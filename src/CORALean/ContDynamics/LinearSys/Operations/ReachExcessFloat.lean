module

public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepExcessFloat
public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox

@[expose] public section

/-!
# How far a float sampled run reaches beyond the exact held-input one

The run's own part of `reachErrorFloat`, everything but the input enclosures'
error boxes: `R₀`'s error box at `j = 0`, then per step the previous excess
carried by `[e^{AΔt}]`, the float step's excess `timePointStepExcessFloat`, and
the reduction's box `reduceGirardBox`.

The recursion recomputes the run at every step, so `k` steps cost `O(k²)` run
steps: a budget for a short horizon, not a production loop.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float run's own excess over the exact held-input sampled set after `j` steps: `R₀`'s
error box, then the previous excess through `[e^{AΔt}]`, each step's float excess and its
reduction's box. -/
def LinearSys.reachExcessFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => R₀.I_error.zonotope                                              -- E(R₀)
  | j + 1 =>
    let eAΔt := sys.expIntervalFloat Δt Δt η                        -- [e^{AΔt}]
    let P := sys.inputSolutionFloat Δt η U                          -- the input set, in floats
    let Rj := (sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])   -- R_j
      ⟨R₀, P, 0, j⟩ ⟨o, ho⟩
    let W := sys.timePointStepInputFloat Δt η Rj U                  -- [e^{AΔt}] R_j ⊞ P
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eAΔt
        (sys.reachExcessFloat Δt η o ho R₀ U j) ⊞                   -- carried excess
      sys.timePointStepExcessFloat Δt η Rj U) ⊞                     -- the step's own
      Zonotope.reduceGirardBox W o                                  -- the reduction's

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
