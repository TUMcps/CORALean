import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
import CORALean.ContSet.HPolytope.Float.Operations.RecipUp

/-!
# `HPolytope.normalizeRows` over a floating-point scalar

CORA's `@polytope/normalizeConstraints` at the types `'A'` and `'Ae'`: every inequality row and
every equality row is divided by its 2-norm. On the stored floats the divisor is the factor
`recipUp (normUp p aᵢ)`, `1 / ‖aᵢ‖₂` with the norm rounded up by `p` Newton steps and the quotient
rounded up, or `1` for a row whose norm is not certified positive (CORA leaves a zero row alone),
and `scaleRows` multiplies by it, paying the rounding on the right-hand side over the box `dom`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every row multiplied by `1 / ‖row‖₂` rounded up, the rounding moved to the right-hand sides. -/
def HPolytope.normalizeRows (p : ℕ) (P : HPolytope 𝕋 n) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 n :=
  P.scaleRows (HPolytope.rowScale p P) (fun i => HPolytope.recipUp (normUp p (P.Ae i))) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
