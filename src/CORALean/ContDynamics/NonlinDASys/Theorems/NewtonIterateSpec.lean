module

public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate

@[expose] public section

/-!
# What the iteration returns

A returned point is `z + step z` for an iterate `z` whose step the test accepted. This is the
stopping test CORA makes, on the step and not on the residual: nothing is said of the point's
distance to a root, only that the last step was small.

## Inputs
* `V` – vector type
* `step` – Newton step
* `small` – smallness test on a step

## Hypotheses
* none

## Conclusion
* a returned point is one step past an iterate whose step was accepted
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A returned point is one step past an iterate whose step `small` accepts. -/
theorem newtonIterate_spec {V : Type} [Add V] (step : V → V) (small : V → Bool) :
    ∀ (fuel : ℕ) (y y' : V), newtonIterate step small fuel y = some y' →
      ∃ z, y' = z + step z ∧ small (step z) = true
  | 0, _, _, h => by simp [newtonIterate] at h
  | fuel + 1, y, y', h => by
    unfold newtonIterate at h
    by_cases hs : small (step y) = true
    · rw [if_pos hs] at h
      exact ⟨y, (Option.some.inj h).symm, hs⟩
    · rw [if_neg hs] at h
      exact newtonIterate_spec step small fuel _ y' h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
