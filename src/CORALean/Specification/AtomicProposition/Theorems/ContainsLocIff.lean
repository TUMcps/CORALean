module

public import CORALean.Specification.AtomicProposition.Operations.Basic

@[expose] public section

/-!
# Which locations a proposition contains

`containsLoc(ap,loc)` is true exactly when `locs` is empty (every location is allowed) or lists the
location.

## Inputs
* `ap` – atomic proposition
* `loc` – location

## Hypotheses
* none

## Conclusion
* the location is allowed iff `locs` is empty or lists it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem AtomicProposition.containsLoc_iff (ap : AtomicProposition S n) (loc : ℕ) :
    ap.containsLoc loc = true ↔ ap.locs = [] ∨ loc ∈ ap.locs := by
  unfold AtomicProposition.containsLoc
  by_cases h : ap.locs = [] <;> simp [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
