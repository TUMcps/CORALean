module

public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
public import CORALean.ContSet.HPolytope.Float.Operations.RecipUp

@[expose] public section

/-!
# `HPolytope.normalizeRows` over a floating-point scalar

CORA's `@polytope/normalizeConstraints` at the types `'A'` and `'Ae'`: every inequality row and
every equality row is divided by its 2-norm. On the stored floats the divisor is the factor
`recipUp (normUp p aᵢ)`, `1 / ‖aᵢ‖₂` with the norm rounded up by `p` Newton steps and the quotient
rounded up, or `1` for a row whose norm is not certified positive (CORA leaves a zero row alone),
and `scaleRows` multiplies by it, paying the rounding on the right-hand side over the box `dom`.
A polytope whose box is certified empty keeps its equalities; one with a box has it folded into
the rows first (`absorbRounding`), the equalities written as inequality pairs.
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

/-- Every row multiplied by `1 / ‖row‖₂` rounded up, the rounding moved to the right-hand sides. -/
def HPolytope.normalizeRows (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the rows as stored when the box is certified empty, else with the box folded in
  let Q := if P.isErrFree then P else P.absorbRounding
  Q.scaleRows (HPolytope.rowScale p Q) (fun i => HPolytope.recipUp (normUp p (Q.Ae i))) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
