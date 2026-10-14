module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual

@[expose] public section

/-!
# `PolyZonotope.exactPlus`

CORA's `@polyZonotope/exactPlus` over a floating-point scalar: the two operands
share their dependent factors, so the generator blocks and the exponent matrices
are appended side by side over one factor set, and the sum is taken point by
point at a common factor value rather than over all pairs as `plus` does.

The shape is `plus`'s, and so is the rounding: the generators are copied and the
exponents are over ℕ, so only the centre rounds, and its `residual` goes into the
box together with the two incoming boxes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.exactPlus (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope (Vec 𝕋 n) where
  p := pZ₁.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := fun i => addDown (pZ₁.c i) (pZ₂.c i)
  G := Fin.append pZ₁.G pZ₂.G
  E := fun k => Fin.append (pZ₁.E k) (pZ₂.E (Fin.cast hp k))
  GI := Fin.append pZ₁.GI pZ₂.GI
  I_error := (pZ₁.I_error.plus pZ₂.I_error).plus (PolyZonotope.centerResidual pZ₁.c pZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
