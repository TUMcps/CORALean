module

public import CORALean.Specification.Operations.Check

@[expose] public section

/-!
# A passed check is the specification, on what the representation denotes

`check`'s two instances each carry their own soundness, so this is a case split and
nothing more. Stated on `toSet s`, not on the set `s` was computed to enclose:
`HoldsOfOuter` is the step from one to the other, and `NN`'s `holds_of_check`, like
every system's, takes both steps at once.

## Inputs
* `spec` – specification
* `S` – computed set

## Hypotheses
* `h` – the check passes

## Conclusion
* the specification holds of the set the representation denotes
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike

variable {ContSet₁ ContSet₂ α : Type} [ContSetLike ContSet₁ α] [ContSetLike ContSet₂ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.check_sound [Contains ContSet₁ ContSet₂] [IsDisjoint ContSet₁ ContSet₂]
    (spec : Specification ContSet₁) (S : ContSet₂) (h : spec.check S) : -- --- CONCL ---
    spec.Holds (toSet S) := by -- --- PROOF ---
  obtain ⟨T, k⟩ := spec
  cases k
  · exact Contains.contains_sound T S h
  · exact IsDisjoint.isDisjoint_sound T S h
  · exact Contains.contains_sound T S h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
