module

public import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianGap

@[expose] public section

/-!
# `PolyZonotope.jacobian`, over a floating-point scalar

CORA's `jacobian(pZ)` for one factor `k`: the polynomial zonotope of the derivative along `k`,
whose generator `i` is `E k i` times the original and whose exponent of `k` is lowered by one;
the centre is `0` and the independent block is dropped. The multiples are stored with the lower
rounding and the gap goes into the error box (`jacobianGap`). The original's error box is not part
of the derivative.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The derivative with respect to the factor `k`. -/
def PolyZonotope.jacobian (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) :
    PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h
  q := 0
  c := fun _ => zero
  G := fun i r => sumDown fun _ : Fin (pZ.E k i) => pZ.G i r
  E := fun k' i => if k' = k then pZ.E k i - 1 else pZ.E k' i
  GI := Fin.elim0
  I_error := PolyZonotope.generatorError (pZ.jacobianGap k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
