module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.convHull`, over a floating-point scalar

CORA's `@capsule/convHull_.m` for two capsules, as the exact layer: the midpoint `c_` of the
centers, the generator `g_` from it to the first center, `(C.c - S.c)/2`, and the larger of the
two radii `‖g‖₂ + r`, here `Capsule.radius`, which counts each operand's error box too. The stored
center and generator are rounded, and what each misses of the exact one (per entry at most half
the gap between the upward and the downward rounding of the same sum or difference) goes into the
error box, as a symmetric box: the center's as it is, the generator's at every segment parameter.
`k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).

## Inputs
* `k` – Newton steps for sqrt
* `C` – first capsule
* `S` – second capsule

## Output
* a capsule enclosing the convex hull of both
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.convHull (k : ℕ) (C S : Capsule 𝕋 n) : Capsule 𝕋 n :=
  let c_ := fun i => half (addUp (C.c i) (S.c i))
  let g_ := fun i => half (subUp (C.c i) (S.c i))
  let cGap := fun i => half (subUp (addUp (C.c i) (S.c i)) (addDown (C.c i) (S.c i)))
  let gGap := fun i => half (subUp (subUp (C.c i) (S.c i)) (subDown (C.c i) (S.c i)))
  let r_ := maximum (C.radius k) (S.radius k)
  ⟨c_, g_, r_, (Interval.symmetric cGap).plus (Interval.symmetric gGap)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
