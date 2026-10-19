module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Monotone in the minuend, antitone in the subtrahend

One statement rather than two, since specialising either side to `subset_rfl`
gives the one-argument form: a larger `S` can only leave more room, and a
smaller `T` can only ask for less.

The direction on `T` is what a caller most often needs — replacing an error set
by a larger one weakens the difference, so an implementation is free to
over-approximate the set it subtracts and still under-approximate the result.

## Inputs
* `S₁` – smaller minuend
* `S₂` – larger minuend
* `T₁` – larger subtrahend
* `T₂` – smaller subtrahend

## Hypotheses
* `hS` – `S₁ ⊆ S₂`
* `hT` – `T₂ ⊆ T₁`

## Conclusion
* `S₁ ⊖ T₁` lies in `S₂ ⊖ T₂`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the first argument and antitone in the second. -/
theorem minkowskiDiff_mono {S₁ S₂ T₁ T₂ : Set α} (hS : S₁ ⊆ S₂) (hT : T₂ ⊆ T₁) :
    minkowskiDiff S₁ T₁ ⊆ minkowskiDiff S₂ T₂ :=
  fun _ hx y hy => hS (hx y (hT hy))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
