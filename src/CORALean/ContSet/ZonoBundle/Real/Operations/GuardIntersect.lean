import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import CORALean.ContSet.HPolytope.Real.Operations.Stack
import CORALean.ContSet.Interval.Real.Operations.EnclosePoints
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `ZonoBundle.guardIntersect`: [1, Sec. VI-A]

The intersection of a reachable bundle with a polytopic guard set, as [1, Sec. VI-A] computes
it: the members converted to halfspaces, `Zonotope.hPolytope` at the caller's directions `Aq`
(the paper's "several parallelotope enclosures" are one choice of them), stacked, which is
the bundle's halfspace description [1, Prop. 4]; intersected with the guard `G`, exactly; and
back to generators by enclosing the intersection's vertices by parallelotopes, `Ψⱼ = Λⱼ
box(Λⱼ⁻¹ V)`, as eq. 2 does with a box of vertices in place of a box of zonotopes.

The vertices of the intersection need vertex enumeration, which the paper hands to "a
standard toolbox" and which nothing here computes: `vert` is that enumerator, an argument,
and the soundness theorem asks it to return points whose hull covers the polytope it is given.
The directions `Λⱼ` are an argument too, as in eq. 2.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q s : ℕ} {κ : Type} [Fintype κ] [Nonempty κ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. VI-A]: halfspaces of the members, stacked and cut by the guard; the cut's
vertices, enclosed by one parallelotope per direction matrix `Λⱼ`. -/
noncomputable def ZonoBundle.guardIntersect (zB : ZonoBundle (Vec ℝ n))
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) (G : HPolytope (Vec ℝ n))
    (vert : HPolytope (Vec ℝ n) → κ → Vec ℝ n) (Λ : Fin s → Mat ℝ n n) :
    ZonoBundle (Vec ℝ n) :=
  let H := HPolytope.stack fun i => (zB.Z i).hPolytope Aq
  let P := H.intersection G
  let V := vert P
  let Ψ := fun j => Zonotope.mtimes (Λ j) (Interval.enclosePoints fun l => (Λ j)⁻¹ *ᵥ V l).zonotope
  ⟨s, Ψ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
