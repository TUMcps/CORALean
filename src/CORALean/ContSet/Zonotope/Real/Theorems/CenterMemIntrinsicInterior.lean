import CORALean.ContSet.Zonotope.Real.Theorems.VectorSpanConstruct
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The centre of a zonotope is in its relative interior

`c` is in the interior of `Z = c + ∑ βⱼgⱼ, |βⱼ| ≤ 1` relative to its affine hull, whatever the
dimension of `Z`: the map `β ↦ ∑ βⱼgⱼ` onto the span of the generators is open (both
finite-dimensional), so it carries the open cube `|βⱼ| < 1` to an open neighbourhood of `0` in that
span, which is the direction of the affine hull (`vectorSpan_construct`). Applied to a facet `Z.face
u`, its centre `c + ∑ sign(u gⱼ)gⱼ` is a point "in the interior of `F`" as [1, Cor. 3.5] asks. Over
any real normed space; `isFullDim_iff` is the full-dimensional case.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.5]: the centre of a zonotope is in its relative interior. -/
theorem Zonotope.center_mem_intrinsicInterior (Z : Zonotope α) :
    Z.c ∈ intrinsicInterior ℝ Z.construct := by -- --- PROOF ---
  let L : (Fin Z.h → ℝ) →ₗ[ℝ] α := Fintype.linearCombination ℝ Z.G
  have hL : ∀ β, L β = ∑ j, β j • Z.G j := fun β => by
    simp [L, Fintype.linearCombination_apply]
  have hc : Z.c ∈ Z.construct := ⟨0, fun _ => by simp, by simp⟩
  have hcA : Z.c ∈ affineSpan ℝ Z.construct := subset_affineSpan ℝ _ hc
  have hdir : (affineSpan ℝ Z.construct).direction = LinearMap.range L := by
    rw [direction_affineSpan, Zonotope.vectorSpan_construct, Fintype.range_linearCombination]
  -- the affine hull, in coordinates about `c`, is the range of `L`
  let φ : affineSpan ℝ Z.construct → LinearMap.range L := fun p =>
    ⟨(p : α) - Z.c, by rw [← hdir]; exact AffineSubspace.vsub_mem_direction p.2 hcA⟩
  have hφ : Continuous φ := (continuous_subtype_val.sub continuous_const).subtype_mk _
  -- `L` onto its range is open, so the open cube maps to an open neighbourhood of `0`
  have hopen : IsOpenMap L.rangeRestrict :=
    L.rangeRestrict.isOpenMap_of_finiteDimensional L.surjective_rangeRestrict
  let U : Set (Fin Z.h → ℝ) := {β | ∀ j, |β j| < 1}
  have hU : IsOpen U := by
    have : U = Set.pi univ fun j => Metric.ball (0 : ℝ) 1 := by
      ext β; simp [U, Set.mem_pi]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun j _ => Metric.isOpen_ball
  rw [mem_intrinsicInterior]
  refine ⟨⟨Z.c, hcA⟩, mem_interior.mpr ⟨φ ⁻¹' (L.rangeRestrict '' U), ?_,
    (hopen U hU).preimage hφ, ?_⟩, rfl⟩
  · rintro p ⟨β, hβ, hp⟩
    have hv := congrArg Subtype.val hp
    simp only [LinearMap.codRestrict_apply, φ] at hv
    refine ⟨β, fun j => (hβ j).le, ?_⟩
    rw [← hL, hv, add_sub_cancel]
  · exact ⟨0, fun j => by simp, by ext; simp [φ]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
