import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# An outer approximation is enough to check a whole list of specifications

Split out of `HoldsOfOuter.lean` (issue #62): the same transfer, one
specification at a time, for `Specification.HoldsAll`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet α : Type} [CORALean.ContSet ContSet α] {X O : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holdsAll_of_outer (specs : List (Specification ContSet)) (h : X ⊆ O)
    (hO : Specification.HoldsAll specs O) : Specification.HoldsAll specs X :=
  fun spec hmem => (spec.holds_of_outer h) (hO spec hmem)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
