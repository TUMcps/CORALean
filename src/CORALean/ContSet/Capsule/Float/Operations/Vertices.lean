module

public import CORALean.ContSet.Capsule.Float.Operations.ArcBox
public import CORALean.ContSet.Capsule.Float.Operations.PiStep
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Operations.Atan2
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.vertices`, over a floating-point scalar

CORA's `vertices_` (planar): the `1001` sampled boundary points, each as a box around the exact
sample, or the centre of a point capsule. The generator angle is bounded by the corner values
`atan2Lo`, `atan2Hi`; the two half circles of `500` points, around `c + g` from `θ - π/2` and
around `c - g` from `θ + π/2` in steps of `π / 499`, then the first point again. The boxes bound
sampled points on the boundary, not vertices (a capsule has none), and a box is not a point of the
boundary.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.vertices (p k : ℕ) (C : Capsule 𝕋 2) : List (Interval (Vec 𝕋 2)) :=
  if C.representsa_point = true then [Interval.point C.c] else
    -- the generator angle `θ`, and `π/2`, as boxes
    let θ : Interval (Vec 𝕋 1) :=
      ⟨fun _ => Interval.atan2Lo p k (C.g 0) (C.g 1), fun _ => Interval.atan2Hi p k (C.g 0) (C.g 1)⟩
    let quarter : Interval (Vec 𝕋 1) := ⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩
    let ctr₁ : Interval (Vec 𝕋 2) :=
      ⟨fun j => addDown (C.c j) (C.g j), fun j => addUp (C.c j) (C.g j)⟩
    let ctr₂ : Interval (Vec 𝕋 2) :=
      ⟨fun j => subDown (C.c j) (C.g j), fun j => subUp (C.c j) (C.g j)⟩
    let step := Capsule.piStep p k
    let half₁ := List.ofFn fun i : Fin 500 =>
      Capsule.arcBox p step ctr₁ (θ.minus quarter) C.r i              -- 500 points, `linspace`
    let half₂ := List.ofFn fun i : Fin 500 =>
      Capsule.arcBox p step ctr₂ (θ.plus quarter) C.r i
    half₁ ++ half₂ ++ [Capsule.arcBox p step ctr₁ (θ.minus quarter) C.r 0]    -- closed

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
