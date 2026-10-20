module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.HybridDynamics.Operations.LinearResetSynchronize
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTarget

@[expose] public section

/-!
# `Transition.synchronize`

CORA's `transition/synchronize` for transitions already lifted to the product (a lone transition,
or all those carrying one synchronization label): the guard is the intersection of the guards
(`synchronizeGuard`), the reset the synchronized reset (`LinearReset.synchronize`), the target the
location tuple `locID` with the participating components moved (`synchronizeTarget`). Not
modelled: CORA's `resolve`, which substitutes the output equations into the input binds of the
reset's input matrix `B`; `Transition` has no `B` (#40), nor mixed linear and nonlinear resets.

## Inputs
* `compIdx` – component indices
* `t` – transitions of the components
* `idStates` – states kept by identity
* `locID` – current locations

## Output
* synchronized transition of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n q k : ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The synchronized transition at the real scalar, the steps in CORA's order. -/
noncomputable def Transition.synchronize (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (fun k => HPolytope ℝ (Vec ℝ k)) (L (compIdx i)) ℝ n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) :
    Transition (fun k => HPolytope ℝ (Vec ℝ k)) (∀ c, L c) ℝ n :=
  -- `guard = fullspace`, then `and_(guard, transList(i).guard, 'exact')` for each `i`
  let guard := Transition.synchronizeGuard (fun i => (t i).guard)
  -- `reset_sync = synchronize(resets, idStates)`
  let reset_sync := LinearReset.synchronize (fun i => (t i).W) (fun i => (t i).w) idStates
  -- `target(compIdx) = transList(i).target`
  let target := Transition.synchronizeTarget locID compIdx (fun i => (t i).target)
  { guard := guard, W := reset_sync.1, w := reset_sync.2, target := target }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
