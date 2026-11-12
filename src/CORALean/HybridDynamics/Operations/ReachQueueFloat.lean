module

public import CORALean.HybridDynamics.Operations.ReachQueueLoopFloat

@[expose] public section

/-!
# `HybridAutomaton.reachQueueFloat`

CORA's `hybridAutomaton/reach` at float zonotopes, halfspace invariants and hyperplane guards
(`zonoGirard` with the `'box'` basis): the queue starts with `X₀` at `ℓ₀`, the entry at the front is
analysed (`reachQueueStepFloat`) and the entries of its crossings join the end, until the queue is
empty. The branches come in the order of analysis. `none` where a step fails or `fuel` entries do
not empty the queue.

## Inputs
* `HA` – hybrid automaton
* `B` – basis
* `options` – reach options
* `tStart` – start time
* `ℓ₀` – initial location
* `X₀` – initial zonotope

## Output
* the branches, none on failure
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] [DecidableEq L]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The branches of the stays from `X₀` at `ℓ₀` at the time `tStart`, in the order of analysis. -/
def HybridAutomaton.reachQueueFloat
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (B : Mat 𝕋 n n)
    (options : HybridReachOptions L 𝕋) (tStart : ℚ) (ℓ₀ : L) (X₀ : Zonotope (Vec 𝕋 n)) :
    Option (List (HybridBranch L 𝕋 n)) :=
  HA.reachQueueLoopFloat B options options.fuel [⟨ℓ₀, X₀, tStart, tStart, none⟩] []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
