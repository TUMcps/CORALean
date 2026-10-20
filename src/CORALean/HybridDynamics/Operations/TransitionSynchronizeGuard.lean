module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# `Transition.synchronizeGuard`

The guard of the synchronized transition in CORA's `transition/synchronize`: `fullspace`
intersected with each guard in turn, as `and_(guard, transList(i).guard, 'exact')` does, here at
polytope guards (`HPolytope.intersection`, the stacked rows after each error box has been folded
into them).

## Inputs
* `g` – guards of the components

## Output
* intersection of the guards
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The guard of the synchronized transition: `fullspace` and then each guard, `and_` in turn. -/
def Transition.synchronizeGuard (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  (List.finRange q).foldl (fun guard i => HPolytope.intersection guard (g i))
    (HPolytope.fullspace 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
