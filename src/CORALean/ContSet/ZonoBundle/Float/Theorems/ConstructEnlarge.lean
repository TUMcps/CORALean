module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
public import CORALean.ContSet.ContSet.Operations.EnlargeScalar

@[expose] public section

/-!
# The enlarged bundle is the intersection of the enlarged members

By definition: `CORA` enlarges each zonotope about its own center, and a bundle denotes the
intersection of its members, so the result is the intersection of the enlarged members and not
the enlargement of the intersection about a common center.

## Inputs
* `zB` – float zonotope bundle
* `f` – enlargement factor per coordinate

## Hypotheses
* none

## Conclusion
* the enlarged bundle is the intersection of the enlarged members
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.construct_enlarge (zB : ZonoBundle (Vec 𝕋 n)) (f : Vec 𝕋 n) :
    (zB.enlarge f).construct = ⋂ i, (ContSet.enlargeScalar (S := 𝒵[𝕋])
      (zB.Z i) f).construct :=
  ZonoBundle.construct_eq_iInter _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
