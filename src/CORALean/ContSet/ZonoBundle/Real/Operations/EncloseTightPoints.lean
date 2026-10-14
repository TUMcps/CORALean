module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.EnclosePointsStursberg
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `ZonoBundle.encloseTightPoints`

The bundle of CORA's `@zonoBundle/encloseTight(zB1, zB2, W)`, for a point family `V` (the vertices
of the two bundles): for each transformation `W{i}` the zonotope
`W{i} * zonotope(interval.enclosePoints(pinv(W{i}) V))`, the box of the points in the coordinates
`W{i}` spans, mapped back; and one more, `zonotope.enclosePoints(V, 'stursberg')`. `pinv(W{i})`
is the matrix inverse, which is `pinv` for an invertible `W{i}`; the orthogonal `U` of the
Stursberg enclosure is CORA's `svd(cov(.))`, an argument as in `Zonotope.enclosePointsStursberg`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n r N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The boxes in each `W{i}`'s coordinates and the Stursberg zonotope, for the points `V`. -/
noncomputable def ZonoBundle.encloseTightPoints [NeZero N] (V : Fin N → Vec ℝ n)
    (W : Fin r → Mat ℝ n n) (U : Mat ℝ n n) : ZonoBundle (Vec ℝ n) where
  k := r + 1
  Z := Fin.snoc (α := fun _ => Zonotope (Vec ℝ n))
    (fun i =>
      let V_W := fun j => (W i)⁻¹ *ᵥ V j                  -- pinv(W{i}) * V
      let I := Interval.enclosePoints V_W                  -- interval.enclosePoints(...)
      Zonotope.mtimes (W i) I.zonotope)                    -- W{i} * zonotope(I)
    (Zonotope.enclosePointsStursberg V U)                  -- zonotope.enclosePoints(V, 'stursberg')


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
