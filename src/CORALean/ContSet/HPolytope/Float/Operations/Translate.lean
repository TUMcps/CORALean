import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.translate`, over a floating-point scalar

The first operation at this layer that actually rounds, and the one that shows
why the equality right-hand side is an interval.

Shifting moves each bound by what its own row reads off the shift, which is a
dot product and so inexact. An inequality absorbs that by rounding its bound up:
the halfspace only grows. An equality has no single direction to grow in, so
both ends of its interval move outward — down at `inf`, up at `sup` — and the
row stays satisfiable. A point right-hand side could not have done this, and no
ambient error box would have rescued it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.translate (t : Vec 𝕋 n) (P : HPolytope 𝕋 n) : HPolytope 𝕋 n where
  m := P.m
  A := P.A
  b := fun i => addUp (P.b i) (dotUp (P.A i) t)
  me := P.me
  Ae := P.Ae
  be := ⟨fun i => addDown (P.be.inf i) (dotDown (P.Ae i) t),
         fun i => addUp (P.be.sup i) (dotUp (P.Ae i) t)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
