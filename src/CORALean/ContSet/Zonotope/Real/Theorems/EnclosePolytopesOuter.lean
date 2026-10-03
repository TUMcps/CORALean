import CORALean.ContSet.Zonotope.Real.Operations.EnclosePolytopes
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The enclosing zonotope of polytopes encloses them

[1, Prop. 12], whose proof is "omitted as it is analogous to Prop. 8": `Λ⁻¹` maps each
polytope `P_l = conv(V l)` into the hull of the mapped vertices, the box over all vertices
is convex and holds every mapped vertex, so it holds every `Λ⁻¹P_l`; and `Λ` maps it back,
`Λ Λ⁻¹ = I` being where full rank is spent.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 12]: at a full-rank `Λ`, every polytope `conv(V l)` lies in
`Λ box(Λ⁻¹P₁, ..., Λ⁻¹P_μ)`. -/
theorem Zonotope.enclosePolytopes_outer {Λ : Mat ℝ n n} (hΛ : IsUnit Λ.det)
    (V : ι → κ → Vec ℝ n) (l : ι) :
    convexHull ℝ (Set.range (V l))
      ⊆ (Zonotope.enclosePolytopes Λ V).construct := by -- --- PROOF ---
  intro x hx
  set box := Interval.enclosePoints fun v : ι × κ => Λ⁻¹ *ᵥ V v.1 v.2
  -- `Λ⁻¹ x` is in the hull of the mapped vertices of `P_l`, hence in the box
  have hbox : Λ⁻¹ *ᵥ x ∈ box.construct := by
    have himg : Λ⁻¹ *ᵥ x ∈ convexHull ℝ ((Matrix.mulVecLin Λ⁻¹) '' Set.range (V l)) := by
      rw [← LinearMap.image_convexHull]
      exact ⟨x, hx, rfl⟩
    refine convexHull_min ?_ (Interval.convex_construct _) himg
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact Interval.enclosePoints_outer (fun v : ι × κ => Λ⁻¹ *ᵥ V v.1 v.2) (l, k)
  -- and `Λ` maps it back to `x`
  rw [Zonotope.enclosePolytopes, ← Zonotope.mtimes_exact]
  refine ⟨_, Interval.zonotope_contains _ hbox, ?_⟩
  show Λ *ᵥ (Λ⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΛ, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
