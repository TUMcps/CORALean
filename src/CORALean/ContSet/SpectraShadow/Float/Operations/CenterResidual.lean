module

public import CORALean.ContSet.Interval.Float.Operations.Residual
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.centerResidual`

Storing the lower of the two directed roundings of a centre sum leaves this
much to pay into the box. The same box a zonotope pays, written again here rather
than imported, so that the two representations stay independent of each other.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def SpectraShadow.centerResidual (a b : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
