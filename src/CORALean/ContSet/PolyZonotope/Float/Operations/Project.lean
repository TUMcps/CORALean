module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.project` over a floating-point scalar

CORA's `@polyZonotope/project` and [1, Prop. 2.11], at a family of coordinates: the centre and
the rows of both generator blocks at the chosen coordinates, the exponent matrix and the factor
counts untouched, and the error box projected with `Interval.project`. Selecting coordinates
does no arithmetic, so nothing rounds. `dims` may repeat or reorder coordinates; one coordinate
is `dims = fun _ => i` at `m = 1`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.project (pZ : PolyZonotope (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    PolyZonotope (Vec 𝕋 m) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := fun k => pZ.c (dims k)
  G := fun l k => pZ.G l (dims k)
  E := pZ.E
  GI := fun j k => pZ.GI j (dims k)
  err := pZ.err.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
