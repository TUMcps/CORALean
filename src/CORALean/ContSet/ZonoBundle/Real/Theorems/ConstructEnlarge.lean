module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Operations.Enlarge

@[expose] public section

/-!
# The enlarged bundle is the intersection of the enlarged members

By definition: `CORA` enlarges each zonotope about its own center, and a bundle denotes the
intersection of its members, so the result is the intersection of the enlarged members and not
the enlargement of the intersection about a common center.
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

theorem ZonoBundle.construct_enlarge (zB : ZonoBundle (Vec ℝ n)) (f : Vec ℝ n) :
    (zB.enlarge f).construct = ⋂ i, (ContSet.enlarge (S := 𝒵)
      (zB.Z i) f).construct :=
  ZonoBundle.construct_eq_iInter _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
