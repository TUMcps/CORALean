module

public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# `SetIntersection.intersection`

The two lists of members, appended: an intersection of intersections is the intersection of all
their members, so this runs no operation on any member and loses nothing. It is what CORA's
`and_` on two `zonoBundle`s does with their cell arrays of zonotopes, at any member type.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The members of both, appended. -/
def SetIntersection.intersection (I J : SetIntersection S) : SetIntersection S :=
  ⟨I.sets ++ J.sets⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
