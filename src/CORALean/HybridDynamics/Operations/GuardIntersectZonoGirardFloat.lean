module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.HybridDynamics.Operations.ZonoGirardBoxFloat
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Location.guardIntersectZonoGirardFloat`

CORA's `guardIntersect_zonoGirard`, at float zonotopes. In each basis `B`, the cut of a reach set
by the guard `{x | x·n = γ}` along the column `ℓ` of `B` is `[-U(-ℓ), U(ℓ)]`, `U` the dual bound
`Location.zonoGirardUpperFloat` standing for [1, Alg. 3] and [1, Alg. 4]; the intervals of the
reach sets are joined and `B zonotope(I)` is member `i` of the zonoBundle. Left out:
`aux_tightenSet`, `aux_robustProjection` and the `interval.empty` test of a basis: an empty cut is
an interval with `inf > sup`. A bundle of one member is kept a bundle. The sets are `R₀ :: Rs`.

## Inputs
* `Bs` – bases
* `R₀` – initial zonotope
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset

## Output
* bundle of boxes enclosing the guard intersection

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle over the bases `Bs`: member `i` boxes, in `Bs[i]`, the union of the cuts of the
reach sets by the hyperplane. -/
def Location.guardIntersectZonoGirardFloat (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋) : ZonoBundle (Vec 𝕋 n) where
  k := Bs.length
  Z := fun i =>
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bs[i]
      (Location.zonoGirardBoxFloat Bs[i] R₀ Rs nv γ).zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
