module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.CenterMat
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

@[expose] public section

/-!
# An interval matrix times a polynomial zonotope, in floats

`mid(M) pZ`, which keeps the dependency on the factors, plus the box `(M - mid(M)) [pZ]` as
independent generators: what CORA's `mtimes` of an `intervalMatrix` and a `polyZonotope` does to
the generators, with the radius applied to the interval hull of `pZ`.

## Inputs
* `IM` – interval matrix
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope containing `M x` for every `M` in `IM` and `x` in `pZ`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mid(M) pZ`, plus the box of `(M - mid(M))` on the hull of `pZ`, as independent generators. -/
def PolyZonotope.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) :=
  let C := Interval.centerMat IM                                    -- mid(M), stored
  let Rs := Interval.matResidual IM.inf IM.sup C                    -- M - mid(M), a box
  ((PolyZonotope.mtimes C pZ).plus                                  -- mid(M) pZ ⊕ box
    (Interval.mtimesIntervalMat Rs pZ.zonotope.interval).zonotope.ofIndep).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
