import CORALean.Specification.Operations.Check

/-!
# A passed check is the specification, on what the representation denotes

`check`'s two instances each carry their own soundness, so this is a case split and
nothing more. Stated on `construct s`, not on the set `s` was computed to enclose:
`HoldsOfOuter` is the step from one to the other, and `NN`'s `holds_of_check`, like
every system's, takes both steps at once.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {ContSet S α : Type} [CORALean.ContSet ContSet α] [CORALean.ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.check_sound [Contains ContSet S] [IsDisjoint ContSet S]
    (spec : Specification ContSet) (s : S) (h : spec.check s) :
    spec.Holds (construct s) := by -- --- PROOF ---
  obtain ⟨t, k⟩ := spec
  cases k
  · exact Contains.contains_sound t s h
  · exact IsDisjoint.isDisjoint_sound t s h
  · exact Contains.contains_sound t s h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
