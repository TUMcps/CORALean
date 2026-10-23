module

public import CORALean.HybridDynamics.Operations.TransitionSynchronize
public import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeApply
public import CORALean.HybridDynamics.Operations.Basic

@[expose] public section

/-!
# `Transition.synchronize` resets by the sum

The synchronized reset at a point is the sum of the component resets plus the pre-jump value at
`idStates`: exact.

## Inputs
* `compIdx` – component indices
* `t` – transitions of the components
* `idStates` – states kept by identity
* `locID` – current locations
* `x` – state
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* synchronized reset is the sum of the component resets
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n q k : ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The synchronized reset at a point: the sum of the component resets, plus the pre-jump value
at `idStates`. -/
theorem Transition.synchronize_reset (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (fun k => HPolytope ℝ (Vec ℝ k)) (L (compIdx i)) ℝ n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) (x : Vec ℝ n) (i : Fin n) : -- --- CONCL ---
    (Transition.synchronize compIdx t idStates locID).reset x i =
      (if i ∈ idStates then x i else 0) + ∑ j, ((t j).reset x) i := by -- --- PROOF ---
  simpa [Transition.synchronize, Transition.reset] using
    LinearReset.synchronize_apply (fun j => (t j).W) (fun j => (t j).w) idStates x i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
