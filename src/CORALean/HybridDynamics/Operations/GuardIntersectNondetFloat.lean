module

public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Location.guardIntersectNondetFloat`

CORA's `guardIntersect_nondetGuard`, at float zonotopes. For each basis `B_i` the reach sets are
boxed in that basis, `I_i = ⋃_j interval(B_iᵀ R_j)`, the parallelotope `B_i I_i` is cut to the
guard as a conZonotope, and the cut is boxed again in the basis. The sets `B_i interval(B_iᵀ cZ_i)`
form a zonoBundle, one member per basis.

The sets are `R₀ :: Rs`, never empty: CORA's `interval.empty` start and its empty-box
special case are not needed. The guard is a conZonotope, which is what CORA's `and_` converts it
to. A bundle of one member is kept a bundle; CORA returns the zonotope itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle over the bases `Bs`: member `i` boxes the sets in `Bs[i]`, cut to the guard. -/
def Location.guardIntersectNondetFloat (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (guard : ConZonotope 𝕋 (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) where
  k := Bs.length
  Z := fun i =>
    let B := Bs[i]
    let box := (Rs.map fun R => (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ
      R).interval).foldl Interval.or
      (Mtimes.mtimes (𝕄 := Mat 𝕋)  -- I_i, the sets boxed in the basis
        (S := 𝒵[𝕋]) Bᵀ R₀).interval
    let cZ := ConZonotope.intersection
      (Zonotope.conZonotope (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B
      box.zonotope)) guard                               -- the parallelotope cut to the guard
    Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B
      (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ).interval.zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
