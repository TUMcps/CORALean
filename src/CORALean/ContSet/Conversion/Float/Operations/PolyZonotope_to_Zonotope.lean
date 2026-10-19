module

public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, over a floating-point scalar

`PolyZonotope.zonotope` frees every dependent generator. `PolyZonotope.zonotopeEven` is CORA's
`zonotope(pZ)`: an all-even column keeps half its generator and moves the other half into the
center, a constant column moves whole (the exact layer's `evenWeight`), the others stay. The
generators are exact (`half` is), and so is every term of the center's shift; only their sum
rounds, so the center is kept and the shift goes into the error box as the interval of its sums
rounded down and up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent generators, then the independent ones, side by side. -/
def PolyZonotope.zonotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI
  I_error := pZ.I_error

def ConPolyZono.zonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  cPZ.polyZonotope.zonotope

/-- CORA's `zonotope(pZ)`: the even columns halved, their other half and the constant columns
moved into the center, that shift paid into the error box. -/
def PolyZonotope.zonotopeEven (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  -- `G(:, ~isEvenColumn)`, `0.5*Gquad`, and nothing of a constant column
  let Gw : Fin pZ.h → Vec 𝕋 n := fun l i =>
    if ∀ k, pZ.E k l = 0 then zero else if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i
  -- the center's shift `0.5*sum(Gquad, 2)`, a constant column whole
  let t : Fin pZ.h → Vec 𝕋 n := fun l i =>
    if ∀ k, pZ.E k l = 0 then pZ.G l i else if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else zero
  { h := pZ.h + pZ.q
    c := pZ.c
    G := Fin.append Gw pZ.GI
    I_error := pZ.I_error.plus ⟨fun i => sumDown fun l => t l i, fun i => sumUp fun l => t l i⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
