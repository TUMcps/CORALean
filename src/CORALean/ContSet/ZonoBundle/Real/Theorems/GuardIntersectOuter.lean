module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Operations.GuardIntersect
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Real.Theorems.StackExact
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import Mathlib.Analysis.Convex.Hull
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeContains

@[expose] public section

/-!
# The guard intersection of a bundle is enclosed

[1, Sec. VI-A]: `Z_∩ ∩ G ⊆ {Ψ₁, ..., Ψ_s}_∩`. Each member lies in its halfspace enclosure, so
the bundle lies in the stack; the guard is kept exactly, so `Z_∩ ∩ G` lies in the cut `P`; and
when the enumerator's points `V` have `P` in their convex hull, `Λⱼ⁻¹ P` lies in the hull of
`Λⱼ⁻¹ V`, hence in its box, and `P` in `Λⱼ box(Λⱼ⁻¹ V)` for every invertible `Λⱼ`. The
paper claims no tightness, and none is claimed here.

## Inputs
* `zB` – zonotope bundle
* `Aq` – directions for the halfspace conversion
* `G` – guard polytope
* `vert` – vertex enumerator
* `Λ` – parallelotope direction matrices

## Hypotheses
* `hvert` – the vertices' hull covers the intersection polytope
* `hΛ` – every direction matrix is invertible

## Conclusion
* the bundle intersected with the guard is contained in the result

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q s : ℕ} {κ : Type} [Fintype κ] [Nonempty κ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. VI-A]: at a vertex enumerator covering the cut and invertible directions, the
result encloses the bundle cut by the guard. -/
theorem ZonoBundle.guardIntersect_outer (zB : ZonoBundle (Vec ℝ n))
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) (G : HPolytope (Vec ℝ n))
    (vert : HPolytope (Vec ℝ n) → κ → Vec ℝ n) (Λ : Fin s → Mat ℝ n n)
    (hvert : ((HPolytope.stack fun i => (zB.Z i).hPolytope Aq).intersection G).construct
      ⊆ convexHull ℝ
        (Set.range (vert ((HPolytope.stack fun i => (zB.Z i).hPolytope Aq).intersection G))))
    (hΛ : ∀ j, IsUnit (Λ j).det) : -- --- CONCL ---
    zB.construct ∩ G.construct
      ⊆ (zB.guardIntersect Aq G vert Λ).construct := by -- --- PROOF ---
  set P := (HPolytope.stack fun i => (zB.Z i).hPolytope Aq).intersection G
  rintro x ⟨hx, hxG⟩
  -- the bundle and the guard, inside the cut
  have hxP : x ∈ P.construct := by
    rw [← HPolytope.intersection_exact, HPolytope.stack_exact]
    refine ⟨Set.mem_iInter.mpr fun i => Zonotope.hPolytope_contains _ Aq ?_, hxG⟩
    exact SetIntersection.mem_construct_ofFn.mp hx i
  have hxV := hvert hxP
  -- and the cut, inside every parallelotope
  rw [ZonoBundle.construct_eq_iInter]
  show x ∈ ⋂ j, (Zonotope.mtimes (Λ j)
    (Interval.enclosePoints fun l => (Λ j)⁻¹ *ᵥ vert P l).zonotope).construct
  refine Set.mem_iInter.mpr fun j => ?_
  have hbox : (Λ j)⁻¹ *ᵥ x ∈ (Interval.enclosePoints fun l => (Λ j)⁻¹ *ᵥ vert P l).construct := by
    have himg : (Λ j)⁻¹ *ᵥ x ∈ convexHull ℝ ((Matrix.mulVecLin (Λ j)⁻¹) '' Set.range (vert P)) := by
      rw [← LinearMap.image_convexHull]
      exact ⟨x, hxV, rfl⟩
    refine convexHull_min ?_ (Interval.convex_construct _) himg
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact Interval.enclosePoints_outer _ l
  rw [← Zonotope.mtimes_exact]
  refine ⟨_, Interval.zonotope_contains _ hbox, ?_⟩
  show Λ j *ᵥ ((Λ j)⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hΛ j), Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
