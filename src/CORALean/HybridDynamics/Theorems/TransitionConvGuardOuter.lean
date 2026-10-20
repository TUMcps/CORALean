module

public import CORALean.HybridDynamics.Operations.TransitionConvGuard
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionOuter

@[expose] public section

/-!
# `Transition.convGuard` contains guard and invariant

The new guard contains the intersection of the old one and the invariant: stacking the rows
loses nothing, and folding each error box into its rows (`HPolytope.intersection`) only enlarges.
The reset and the target are untouched.

## Inputs
* `e` – transition
* `inv` – invariant polytope

## Hypotheses
* none

## Conclusion
* the new guard contains the guard intersected with the invariant
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `construct` of the cut guard contains the guard's intersection with the invariant. -/
theorem Transition.convGuard_guard_outer (e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (inv : HPolytope 𝕋 (Vec 𝕋 n)) :
    e.guard.construct ∩ inv.construct ⊆ (e.convGuard inv).guard.construct :=
  HPolytope.intersection_outer e.guard inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
