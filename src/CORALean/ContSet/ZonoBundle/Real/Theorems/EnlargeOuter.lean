module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Enlarge
public import CORALean.ContSet.ContSet.Theorems.EnlargeOuter

@[expose] public section

/-!
# Each member of an enlarged bundle encloses the scaling of its own member

The bundle denotes an intersection of its members, and each member is scaled about its own
centre. So the statement is per member: the image of member `i` under `x ↦ cᵢ + f ⊙ (x - cᵢ)`
lies in member `i` of the result, and the result is the intersection of those members
(`construct_enlarge`). It is not a statement about the image of the intersection: the maps differ
from member to member, so the image of the intersection need not lie in the intersection of the
images, and nothing here claims it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.enlarge_outer (zB : ZonoBundle (Vec ℝ n)) (f : Vec ℝ n) (i : Fin zB.k) :
    (fun x : Vec ℝ n => (zB.Z i).c + fun j => f j * (x j - (zB.Z i).c j)) ''
      (zB.Z i).construct ⊆ ((zB.enlarge f).Z i).construct :=
  ContSet.enlarge_outer (S := 𝒵) (𝕋 := ℝ) (zB.Z i) f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
