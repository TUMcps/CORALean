import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll
import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Float.Operations.Parallelotope
import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
import CORALean.ContSet.Interval.Float.Operations.Or
import CORALean.ContSet.Interval.Float.Operations.Magnitude

/-!
# `ZonoBundle.encloseTight`, over a floating-point scalar

CORA's `@zonoBundle/encloseTight(zB1, zB2, W)`: for each `W{i}` the zonotope
`W{i} * zonotope(interval.enclosePoints(pinv(W{i}) V))`, `V` the vertices of the two bundles,
and one more, `zonotope.enclosePoints(V, 'stursberg')`. Without vertex enumeration the box of
`pinv(W{i}) V` is taken as the hull of the two bundles' boxes in those coordinates
(`intervalAll` of each mapped bundle), which holds it. `pinv(W{i})` is a candidate
`Zonotope.basisInverse` and the Stursberg basis `U` is undone by `Uᵀ`; `parallelotope` pays what
either inverse misses, for points within the two bundles' boxes, so neither an invertible `W{i}`
nor an orthogonal `U` is assumed. The Stursberg box centred on the points' mean is the same set
as the box in `U`'s coordinates, so the mean is not formed.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `encloseTight(zB1, zB2, W)`, for the Stursberg basis `U`. -/
def ZonoBundle.encloseTight (zB₁ zB₂ : ZonoBundle 𝕋 n) (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k)
    (W : Fin r → Mat 𝕋 n n) (U : Mat 𝕋 n n) : ZonoBundle 𝕋 n :=
  let m := maximumOver ((zB₁.intervalAll hk₁).or (zB₂.intervalAll hk₂)).magnitude -- reach of V
  let box := fun H : Mat 𝕋 n n =>                       -- interval.enclosePoints(H V)
    ((zB₁.mtimes H).intervalAll hk₁).or ((zB₂.mtimes H).intervalAll hk₂)
  { k := r + 1
    Z := Fin.snoc (α := fun _ => Zonotope 𝕋 n)
      (fun i =>
        let H := Zonotope.basisInverse (W i)            -- pinv(W{i}), a candidate
        ZonoBundle.parallelotope (W i) H (box H) m)     -- W{i} * zonotope(box)
      -- zonotope.enclosePoints(V, 'stursberg'), the box in `U`'s coordinates
      (ZonoBundle.parallelotope U U.transpose (box U.transpose) m) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
