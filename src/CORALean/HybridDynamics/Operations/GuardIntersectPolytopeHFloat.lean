module

public import CORALean.ContSet.ConZonotope.Float.Operations.IntersectHPolytope
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalBox
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Location.guardIntersectPolytopeHFloat`

CORA's `guardIntersect_polytope` and `guardIntersect_conZonotope` with a polytope guard, at float
zonotopes: as `Location.guardIntersectPolytopeFloat`, each reach set is cut to the guard, here by
`ConZonotope.intersectHPolytope`, and each basis boxes the union of the cuts, here by
`ConZonotope.box` (`k` contraction passes, dual certificates, or both), which keeps the
constraints as CORA's linear programs do. A hyperplane or halfspace guard is an `HPolytope` with
an equality or an inequality row. Left out as there: CORA's enclosure of each `R_j` by a polytope
and its vertices. The sets are `R₀ :: Rs`, never empty.

## Inputs
* `m` – method of the box of a cut: Fourier-Motzkin passes, simplex certificates or both
* `Bs` – bases
* `R₀` – initial zonotope
* `Rs` – reach sets
* `guard` – halfspace polytope guard

## Output
* bundle of boxes enclosing the guard intersection
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle over the bases `Bs`: member `i` boxes, in `Bs[i]`, the union of the reach sets cut
to the guard. -/
def Location.guardIntersectPolytopeHFloat (m : ConZonotope.BoxMethod) (Bs : List (Mat 𝕋 n n))
    (R₀ : Zonotope (Vec 𝕋 n)) (Rs : List (Zonotope (Vec 𝕋 n))) (guard : HPolytope 𝕋 (Vec 𝕋 n)) :
    ZonoBundle (Vec 𝕋 n) where
  k := Bs.length
  Z := fun i =>
    let B := Bs[i]
    let cut := fun R : Zonotope (Vec 𝕋 n) =>
      ConZonotope.box m
        (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ
          ((Zonotope.conZonotope R).intersectHPolytope guard))
    let box := (Rs.map cut).foldl Interval.or (cut R₀)   -- boxes of the cuts R_j ∩ guard, joined
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B box.zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
