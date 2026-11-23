module

public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRowsDiv
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `HPolytope.normalizeConstraintsCora`

CORA.cpp's `normalizeConstraints` at its default type `'b'`, in its own order: an inequality row is
divided by the absolute value of its right-hand side, an equality row by the right-hand side itself
(so that the right-hand side of an equality is `1`), a row whose right-hand side is not certified
nonzero by `1`. `HPolytope.normalizeConstraints` multiplies by `1 / |b|` instead, which rounds
differently, and keeps the sign of an equality's right-hand side. `scaleRowsDiv` divides and pays
the rounding on the right-hand sides over the box `dom`, after the polytope's own error box has
been folded into the rows.

## Inputs
* `P` – H-polytope
* `dom` – domain interval

## Output
* every row divided as CORA.cpp divides it, the rounding in the right-hand sides
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The divisor of an inequality row: `|b|` where it is certified positive, else `1`. -/
@[step_of HPolytope.normalizeConstraintsCora]
def HPolytope.step_normDivisorA (b : 𝕋) : 𝕋 :=
  if ltStrict zero (absolute b) then absolute b else one

/-- The divisor of an equality row: `b` where it is certified nonzero, else `1`. -/
@[step_of HPolytope.normalizeConstraintsCora]
def HPolytope.step_normDivisorE (b : 𝕋) : 𝕋 :=
  if ltStrict zero b then b else if ltStrict b zero then b else one


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.normalizeConstraintsCora (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the rows as stored when the box is certified empty, else with the box folded in
  let Q := if P.isErrFree then P else P.absorbRounding
  Q.scaleRowsDiv (fun i => HPolytope.step_normDivisorA (Q.b i))
    (fun i => HPolytope.step_normDivisorE (Q.be i)) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
