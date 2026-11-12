module

public import CORALean.HybridDynamics.Operations.LocationQueueJumpFloat
public import CORALean.HybridDynamics.Operations.LocationPotInt
public import CORALean.HybridDynamics.Operations.LocationStayFloat
public import CORALean.HybridDynamics.Operations.GuardGroups
public import CORALean.ContDynamics.Reach.Operations.StepCount

@[expose] public section

/-!
# `HybridAutomaton.reachQueueStepFloat`

One pass of the loop of CORA's `hybridAutomaton/reach`: the entry at the front of the queue is
analysed in its location. The stay takes `Reach.stepCount` steps from the lower start time,
`Location.stayFloat`; `Location.potInt` lists the guards the sets may meet (the transitions into
`finalLoc` skipped), `Location.guardGroups` groups the hits into crossings and
`Location.queueJumpFloat` makes the entry of each, after `checkFlow` (`options.checkFlow`) has
dropped the sets of the group whose flow points strictly into the invariant. Not modelled: the swap
of a lone hyperplane hit for the time-point set, and the specifications.

## Inputs
* `HA` – hybrid automaton
* `B` – basis
* `options` – reach options
* `idx` – number of the branch
* `p` – queue entry

## Output
* the branch and the entries it adds to the queue, none on failure
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

/-- The branch of the stay of the entry `p`, and the entries of its crossings of guards. -/
def HybridAutomaton.reachQueueStepFloat
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (B : Mat 𝕋 n n)
    (options : HybridReachOptions L 𝕋) (idx : ℕ) (p : HybridPending L 𝕋 n) :
    Option (HybridBranch L 𝕋 n × List (HybridPending L 𝕋 n)) := do
  let ℓ := HA.loc p.loc
  let Δ := ToRat.toRat (options.Δt p.loc)
  let N := Reach.stepCount p.tlo options.tFinal Δ                   -- whole steps to the horizon
  let Rs ← ℓ.stayFloat N { Δt := options.Δt p.loc, η := options.η, ρ := options.ρ } p.set
  let hits := ℓ.potInt Rs options.finalLoc                          -- which guards may be met
  let jumps ← (Location.guardGroups hits).mapM                       -- one entry per crossing
    (ℓ.queueJumpFloat options.checkFlow B Δ idx p.tlo p.thi Rs)
  pure (⟨p.loc, p.parent, Rs, p.tlo, p.thi⟩, jumps.filterMap id)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
