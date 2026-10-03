import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.Global.EuclideanNorm

/-!
# `Capsule.containsPoint`

CORA's `@capsule/contains_.m` for a point `p`, `aux_containsPoint`: project `p - c` on the unit
direction `g_ = g / ‖g‖`; if the projection falls inside the segment (`|proj| < ‖g‖`) the point
is tested against the radius by its distance to the axis, else by its distance to the nearer end
(`aux_inSphere` at `c + g` or `c - g`). CORA's `dist < r | withinTol(dist, r)` is `dist ≤ r` at
tolerance `0`, which is what is written here. The other operand types of `contains_` (sets,
`ellipsoid` by a zonotope outer approximation) are not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_containsPoint(C, p)` at tolerance `0`. A `Prop`, as the real layer cannot decide `≤`. -/
def Capsule.containsPoint (C : Capsule n) (p : Vec ℝ n) : Prop :=
  let ng := ‖C.g‖₂
  let g_ := ng⁻¹ • C.g
  let proj := (p - C.c) ⬝ᵥ g_
  (|proj| < ng ∧ ‖(C.c + proj • g_) - p‖₂ ≤ C.r) ∨
    (¬ |proj| < ng ∧ (‖p - (C.c + C.g)‖₂ ≤ C.r ∨ ‖p - (C.c - C.g)‖₂ ≤ C.r))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
