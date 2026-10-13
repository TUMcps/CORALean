import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
import CORALean.ContSet.HPolytope.Float.Operations.RecipUp

/-!
# `HPolytope.normalizeConstraints` over a floating-point scalar

CORA's `@polytope/normalizeConstraints` at its default type `'b'`: every row is divided by the
absolute value of its right-hand side, so that the right-hand side is `±1`. On the stored floats
the divisor is `recipUp |bᵢ|`, `1 / |bᵢ|` rounded up, or `1` for a right-hand side not certified
nonzero (CORA leaves a zero right-hand side alone), and `scaleRows` multiplies by it, paying the
rounding on the right-hand sides over the box `dom`. An equality's interval is divided by the
absolute value of its lower end; unlike CORA's the divisor is positive, so an equality with a
negative right-hand side keeps its sign (`-1` where CORA's is `1`), the same set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every row multiplied by `1 / |right-hand side|` rounded up, the rounding moved to the
right-hand sides. -/
def HPolytope.normalizeConstraints (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  P.scaleRows (fun i => HPolytope.recipUp (absolute (P.b i)))
    (fun i => HPolytope.recipUp (absolute (P.be.inf i))) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
