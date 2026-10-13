module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Supremum
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# `Zonotope.constrSat`, over a floating-point scalar

CORA's test on the rounded box `interval(C*Z)`: every upper bound strictly below `d`, by
`ltStrict`, which is exact. `true` is certain, `false` only says "not shown".
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.constrSat (Z : Zonotope (Vec 𝕋 n)) (C : Mat 𝕋 m n) (d : Vec 𝕋 m) : Bool :=
  let I := (Zonotope.mtimes C Z).interval
  (List.finRange m).all fun i => ltStrict (I.supremum i) (d i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
