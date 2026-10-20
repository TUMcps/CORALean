module

public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Basic
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
# `Location.guardIntersectPolytopeFloat`

CORA's `guardIntersect_polytope`, at float zonotopes. The reach sets are first cut to the guard,
`cZ_j = R_j ∩ guard` as conZonotopes, and each enclosing method then takes the box of the union of
the cuts in its own basis `B_i` (`box`, `pca` or `flow` differ only there, a parameter here, as in
`guardIntersectNondetFloat`); the boxes form a zonoBundle. Left out: CORA's enclosure of each `R_j`
by a polytope (`aux_conv2polytope`) and its vertices; here the box is of the cut. A bundle of one
member is kept a bundle. The sets are `R₀ :: Rs`, never empty.

## Inputs
* `Bs` – bases
* `R₀` – initial zonotope
* `Rs` – reach sets
* `guard` – constrained zonotope guard

## Output
* bundle of boxes enclosing the guard intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle over the bases `Bs`: member `i` boxes, in `Bs[i]`, the union of the reach sets cut
to the guard. -/
def Location.guardIntersectPolytopeFloat (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (guard : ConZonotope 𝕋 (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) where
  k := Bs.length
  Z := fun i =>
    let B := Bs[i]
    let cut := fun R : Zonotope (Vec 𝕋 n) =>
      (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ
        (ConZonotope.intersection (Zonotope.conZonotope R) guard)).interval
    let box := (Rs.map cut).foldl Interval.or (cut R₀)   -- boxes of the cuts R_j ∩ guard, joined
    Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B box.zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
