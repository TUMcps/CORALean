module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# What storing `plus`'s center leaves to pay

Split out of `Plus.lean` (issue #62): read again by `evalPoly`, by
`ConPolyZono.plus`, and by their matching `Theorems/PlusOuter.lean` and
`Theorems/EvalPolyOuter.lean` files, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def PolyZonotope.centerResidual (a b : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
