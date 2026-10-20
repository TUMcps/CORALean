module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Specification.AtomicProposition.Operations.Basic

@[expose] public section

/-!
# When a point satisfies an atomic proposition

A point `x` of the ambient space satisfies the proposition at a location `loc` when the location
is allowed and the coordinates `dims` of `x` lie in the proposition's set. This is what
`evaluatePoint` decides for a point and what `canBeTrue` and `canBeFalse` bound over a set.

## Inputs
* `ap` – atomic proposition
* `x` – point of the ambient space
* `loc` – location

## Output
* the proposition holds at the point and location
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` satisfies `ap` at `loc`. -/
def AtomicProposition.Holds (ap : AtomicProposition S n) (x : Vec ℝ n) (loc : ℕ) : Prop :=
  ap.containsLoc loc = true ∧ ap.readPoint x ∈ construct ap.set

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
