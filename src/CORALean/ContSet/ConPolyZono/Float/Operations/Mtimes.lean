module

public import CORALean.ContSet.ConPolyZono.Float.Operations.MtimesResidual
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.mtimes`

`PolyZonotope.mtimes` with the constraint system carried along untouched. That
it *is* untouched is the whole content: the constraints live on the factors, a
map of the ambient space moves no factor, and so `A`, `b` and `R` are copied
rather than recomputed — which is the only way a constraint block can cross a
float layer at all.

The dimension variables are `k` and `n` rather than the usual `m` and `n`: the
structure already has a field named `m`.

## Inputs
* `M` – linear map
* `cPZ` – constrained polynomial zonotope

## Output
* image under the linear map
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.mtimes (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 k) where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  c := mulVecDown M cPZ.c
  G := fun l => mulVecDown M (cPZ.G l)
  E := cPZ.E
  GI := fun j => mulVecDown M (cPZ.GI j)
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  cons_dom := cPZ.cons_dom
  I_error := (Interval.mtimes M cPZ.I_error).plus (ConPolyZono.mtimesResidual M cPZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
