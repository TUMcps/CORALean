module

public import CORALean.HybridDynamics.Operations.ReachQueueStepFloat

@[expose] public section

/-!
# `HybridAutomaton.reachQueueLoopFloat`

The loop of CORA's `hybridAutomaton/reach`: the entry at the front of the queue is analysed
(`reachQueueStepFloat`, which numbers the branch by those so far) and the entries of its crossings
join the end, until the queue is empty. `none` where a step fails or the fuel is spent first.

## Inputs
* `HA` – hybrid automaton
* `Bf` – the basis of a crossing, from the guard normal and offset and the sets that meet the guard
* `options` – reach options
* `f` – fuel
* `q` – queue
* `acc` – branches so far

## Output
* the branches in the order of analysis, none on failure
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

/-- The branches after `f` more entries are analysed from the queue `q`, after `acc`. -/
def HybridAutomaton.reachQueueLoopFloat
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (Bf : BasisRule 𝕋 n)
    (options : HybridReachOptions L 𝕋) (f : ℕ) (q : List (HybridPending L 𝕋 n))
    (acc : List (HybridBranch L 𝕋 n)) : Option (List (HybridBranch L 𝕋 n)) :=
  match f, q with
  | 0, _ => none                                                    -- the fuel is spent
  | _ + 1, [] => some acc                                           -- nothing left to analyse
  | f + 1, p :: q => do
    let (br, js) ← HA.reachQueueStepFloat Bf options acc.length p     -- the front of the queue
    HybridAutomaton.reachQueueLoopFloat HA Bf options f (q ++ js) (acc ++ [br])   -- its jumps join

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
