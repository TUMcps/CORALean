module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.HybridDynamics.Operations.LinearResetSynchronizeFloat
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTarget

@[expose] public section

/-!
# `Transition.synchronize` in directed rounding

CORA's `transition/synchronize` (`Transition.synchronize`) at a float scalar. The guard and the
target are what the real one computes: stacking the rows of polytope guards and moving the
participating components are exact at any scalar (`synchronizeGuard`, `synchronizeTarget`). The
reset sum is not, so the synchronized reset is the interval reset `LinearReset.synchronizeFloat`
returns, stored entry by entry: `Transition` asks nothing of its scalar, and at `Interval 𝕋` its
`W` and `w` are an interval matrix and an interval vector. Soundness is
`Transition.synchronizeFloat_encloses`.

## Inputs
* `compIdx` – component indices
* `t` – transitions of the components
* `idStates` – states kept by identity
* `locID` – current locations

## Output
* synchronized transition with interval reset
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The synchronized transition at a float scalar, the steps in CORA's order; its reset has
interval coefficients. -/
def Transition.synchronizeFloat (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) (L (compIdx i)) 𝕋 n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) :
    Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) (∀ c, L c) (Interval 𝕋) n :=
  -- `guard = fullspace`, then `and_(guard, transList(i).guard, 'exact')` for each `i`
  let guard := Transition.synchronizeGuard (fun i => (t i).guard)
  -- `reset_sync = synchronize(resets, idStates)`, as lower and upper bounds
  let reset_sync := LinearReset.synchronizeFloat (fun i => (t i).W) (fun i => (t i).w) idStates
  -- `target(compIdx) = transList(i).target`
  let target := Transition.synchronizeTarget locID compIdx (fun i => (t i).target)
  { guard := guard,
    W := fun a b => ⟨reset_sync.1.1 a b, reset_sync.1.2 a b⟩,
    w := fun a => ⟨reset_sync.2.1 a, reset_sync.2.2 a⟩,
    target := target }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
