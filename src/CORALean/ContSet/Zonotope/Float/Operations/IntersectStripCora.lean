module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.intersectStripCora`

CORA.cpp's `intersectStrip` at a given gain `Λ`: the center is `c + Λ (y - C c)`, the generators
`(I - Λ C) G` then `Λ diag(φ)`. `Zonotope.intersectStrip` forms the center as `(I - Λ C) c + Λ y`,
the same real number in another rounding. The zonotope is centered at the origin and the strip
moved by `C c`; the interval `y - C c` gives the lower end as the new measurement and its width,
rounded up, widens `φ` (nothing at `nearest`, where it is a point). `c` is added back at the end.

## Inputs
* `C` – measurement matrix
* `φ` – strip half-widths
* `y` – measurement
* `Λ` – weight matrix
* `Z` – zonotope

## Output
* zonotope enclosing the intersection with the strip
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `C c`, rounded outward: a column of `p` entries. -/
@[step_of Zonotope.intersectStripCora]
def Zonotope.step_stripCenterImage (C : Mat 𝕋 p n) (c : Vec 𝕋 n) : Interval (Mat 𝕋 p 1) :=
  Interval.matMul (Interval.point C) (Interval.point fun j (_ : Fin 1) => c j)

/-- The lower end of `y - C c`. -/
@[step_of Zonotope.intersectStripCora]
def Zonotope.step_stripShiftedY (C : Mat 𝕋 p n) (y : Vec 𝕋 p) (c : Vec 𝕋 n) : Vec 𝕋 p :=
  fun i => subDown (y i) ((Zonotope.step_stripCenterImage C c).sup i 0)

/-- The half-width `φ` plus the width of `y - C c`, rounded up. -/
@[step_of Zonotope.intersectStripCora]
def Zonotope.step_stripShiftedPhi (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (c : Vec 𝕋 n) : Vec 𝕋 p :=
  fun i => addUp (φ i) (subUp (subUp (y i) ((Zonotope.step_stripCenterImage C c).inf i 0))
    (Zonotope.step_stripShiftedY C y c i))


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.intersectStripCora (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : Mat 𝕋 n p)
    (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  Zonotope.plus (Zonotope.point Z.c)
    (Zonotope.intersectStrip C (Zonotope.step_stripShiftedPhi C φ y Z.c)
      (Zonotope.step_stripShiftedY C y Z.c) Λ { Z with c := fun _ => zero })

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
