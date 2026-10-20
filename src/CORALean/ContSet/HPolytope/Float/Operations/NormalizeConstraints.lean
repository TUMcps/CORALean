module

public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
public import CORALean.ContSet.HPolytope.Float.Operations.RecipUp

@[expose] public section

/-!
# `HPolytope.normalizeConstraints` over a floating-point scalar

CORA's `@polytope/normalizeConstraints` at its default type `'b'`: every row is divided by the
absolute value of its right-hand side, so that the right-hand side is `±1`. On the stored floats the
divisor is `recipUp |bᵢ|`, `1 / |bᵢ|` rounded up, or `1` for a right-hand side not certified nonzero
(CORA leaves a zero right-hand side alone), and `scaleRows` multiplies by it, paying the rounding on
the right-hand sides over the box `dom`. A polytope whose box is certified empty keeps its
equalities, rescaled by `scaleRows`; one with a box has it folded into the rows first, the
equalities written as inequality pairs (`absorbRounding`). The divisor is positive, so a row with a
negative right-hand side keeps its sign (`-1` where CORA's is `1`), the same set.

## Inputs
* `P` – H-polytope
* `dom` – domain interval

## Output
* every row multiplied by `1 / |right-hand side|`, rounded up, the rounding in the right-hand sides
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
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
  -- the rows as stored when the box is certified empty, else with the box folded in
  let Q := if P.isErrFree then P else P.absorbRounding
  Q.scaleRows (fun i => HPolytope.recipUp (absolute (Q.b i)))
    (fun i => HPolytope.recipUp (absolute (Q.be i))) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
