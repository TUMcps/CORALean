import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
import CORALean.ContSet.ContSet.Operations.EnlargeScalar

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

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.construct_enlarge (zB : ZonoBundle (Vec 𝕋 n)) (f : Vec 𝕋 n) :
    (zB.enlarge f).construct = ⋂ i, (ContSet.enlargeScalar (S := fun k => Zonotope (Vec 𝕋 k))
      (zB.Z i) f).construct := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
