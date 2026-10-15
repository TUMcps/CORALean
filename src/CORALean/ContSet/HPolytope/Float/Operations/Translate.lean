module

public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqs

@[expose] public section

/-!
# `HPolytope.translate`, over a floating-point scalar

The first operation at this layer that actually rounds.

Shifting moves each bound by what its own row reads off the shift, which is a dot product
and so inexact. An inequality absorbs that by rounding its bound up: the halfspace only
grows. An equality cannot: a rounded right-hand side names a different hyperplane. So an
equality keeps its row, its right-hand side is rounded up, and the shifted points, which read
within the two roundings' gap of it, are moved onto the stored hyperplane (`anchorEqs`): the
step is certified small and paid into the error box, which otherwise moves with the polytope
unchanged. Without a certificate the equality becomes the two inequalities it stands for.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.translate (t : Vec 𝕋 n) (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- every bound moved by what its row reads off `t`, rounded up
  let Q : HPolytope 𝕋 (Vec 𝕋 n) :=
    { P with b := fun i => addUp (P.b i) (dotUp (P.A i) t)
             be := fun i => addUp (P.be i) (dotUp (P.Ae i) t) }
  -- an equality's exact shifted bound lies at most this far below the stored one
  Q.anchorEqs fun i => subUp (Q.be i) (addDown (P.be i) (dotDown (P.Ae i) t))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
