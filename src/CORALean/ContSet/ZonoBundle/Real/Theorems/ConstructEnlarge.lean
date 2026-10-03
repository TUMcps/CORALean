import CORALean.ContSet.ZonoBundle.Real.Operations.Enlarge

/-!
# The enlarged bundle is the intersection of the enlarged members

By definition: `CORA` enlarges each zonotope about its own centre, and a bundle denotes the
intersection of its members, so the result is the intersection of the enlarged members and not
the enlargement of the intersection about a common centre.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.construct_enlarge (zB : ZonoBundle (Vec ℝ n)) (f : Vec ℝ n) :
    (zB.enlarge f).construct = ⋂ i, (ContSet.enlarge (S := fun n => Zonotope (Vec ℝ n))
      (zB.Z i) f).construct := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
