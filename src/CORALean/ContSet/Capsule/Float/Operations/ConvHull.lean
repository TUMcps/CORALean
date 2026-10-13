module

public import CORALean.ContSet.Capsule.Float.Operations.Radius

@[expose] public section

/-!
# `Capsule.convHull`, over a floating-point scalar

CORA's `@capsule/convHull_.m` for two capsules, as the exact layer: the midpoint `c_` of the
centres, the generator `g_` from it to the first centre, `(C.c - S.c)/2`, and the larger of the
two radii `‖g‖₂ + r`. The stored centre and generator are rounded, so the distance of each from the
exact one (per entry at most half the gap between the upward and the downward rounding of the same
sum or difference) is added to the radius as a rounded-up length. `k` is the number of Newton
steps of the roots (`Global/Float/Sqrt`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
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
  let r_ := addUp (maximum (C.radius k) (S.radius k)) (addUp (normUp k cGap) (normUp k gGap))
  ⟨c_, g_, r_⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
