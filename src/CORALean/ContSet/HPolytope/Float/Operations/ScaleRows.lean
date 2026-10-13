import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi

/-!
# `HPolytope.scaleRows`: rows scaled by given numbers, the rounding paid on the right-hand side

CORA's `priv_normalizeConstraints` on the stored floats, with the divisors given: `sA i` for
inequality row `i` and `sE i` for equality row `i`. Every entry of a scaled row is rounded down
(`mulDown`), which names a slightly different halfspace, so the difference is absorbed on the
right-hand side over a box `dom` of interest: an inequality's `b` is raised by the least value
of the deviation `(s a - ã)ᵀ x` (`scaleDevLo`), an equality's interval widened at both ends by
the deviation's range. The scaled polytope contains the original one inside `dom`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` multiplied by `sA i` (`sE i`), the rounding moved to the right-hand sides. -/
def HPolytope.scaleRows (P : HPolytope 𝕋 (Vec 𝕋 n)) (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (dom : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := P.m
  A := fun i j => mulDown (P.A i j) (sA i)
  b := fun i => subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom)
  me := P.me
  Ae := fun i j => mulDown (P.Ae i j) (sE i)
  be :=
    ⟨fun i => subDown (mulDown (P.be.inf i) (sE i)) (HPolytope.scaleDevHi (P.Ae i) (sE i) dom),
     fun i => subUp (mulUp (P.be.sup i) (sE i)) (HPolytope.scaleDevLo (P.Ae i) (sE i) dom)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
