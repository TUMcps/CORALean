import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.Or
import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.HybridDynamics.Operations.ZonoGirardUpperFloat

/-!
# `Location.guardIntersectZonoGirardFloat`

CORA's `guardIntersect_zonoGirard`, at float zonotopes. In each basis `B`, the cut of a reach set
`R_j` by the guard hyperplane `{x | x·n = γ}` along the column `ℓ` of `B` is the interval
`[-U(-ℓ), U(ℓ)]`, `U` the dual bound `Location.zonoGirardUpperFloat` that stands for
[1, Alg. 3] and [1, Alg. 4]; the intervals of the reach sets are joined, and the box
`B zonotope(I)` is member `i` of the zonoBundle.

Left out: `aux_tightenSet` (the cut back by the guard's inequality constraints),
`aux_robustProjection` (a pinned coordinate, right only for a unit normal), and the
`interval.empty` test of a basis, which makes CORA return `[]`: an empty cut is here an interval
with `inf > sup`, and the bundle is returned all the same. A bundle of one member is kept a
bundle; CORA returns the zonotope itself. The sets are `R₀ :: Rs`, never empty.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle over the bases `Bs`: member `i` boxes, in `Bs[i]`, the union of the cuts of the
reach sets by the hyperplane. -/
def Location.guardIntersectZonoGirardFloat (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope 𝕋 n)
    (Rs : List (Zonotope 𝕋 n)) (nv : Vec 𝕋 n) (γ : 𝕋) : ZonoBundle 𝕋 n where
  k := Bs.length
  Z := fun i =>
    let B := Bs[i]
    -- the cut of one reach set along each column `ℓ` of `B`, `[-U(-ℓ), U(ℓ)]`
    let cut : Zonotope 𝕋 n → Interval (Vec 𝕋 n) := fun R =>
      ⟨fun k => neg (Location.zonoGirardUpperFloat R nv γ fun r => neg (Bᵀ k r)),
        fun k => Location.zonoGirardUpperFloat R nv γ (Bᵀ k)⟩
    -- `I`, the cuts joined
    let I := (Rs.map cut).foldl Interval.or (cut R₀)
    Mtimes.mtimes (𝕄 := Mat 𝕋) B I.zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
