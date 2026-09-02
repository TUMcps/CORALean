import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.HPolytope.Real.Theorems.AndExact

/-!
# `VPolytope.and`

Intersection is the operation vertices are worst at — the result's vertices are
generally none of either operand's — so it goes out to halfspaces, where
intersection is free, and comes back.

Both steps are already available and neither is a placeholder: out on directions
the caller names, and back by vertex enumeration, which is exact. So `and` is
exact whenever the directions given contain each operand's facet normals, and
merely encloses otherwise. The directions are the whole of the imprecision.

One extra row goes in on the way out: one operand's own box, so that the
halfspace description is bounded and can be converted back at all. It costs
nothing, the operand already being inside it.

Empty is handled rather than assumed. If the halfspace description turns out to
denote nothing then so does the intersection, and the answer is the empty vertex
list.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}

/-- The intersection as halfspaces, kept bounded by one operand's own box. -/
noncomputable def VPolytope.andH (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    HPolytope (Vec ℝ n) :=
  ((P₁.hPolytope Aq₁).and (P₂.hPolytope Aq₂)).and (Interval.hPolytope P₁.interval)

theorem VPolytope.andH_isCompact (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    IsCompact (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct := by
  refine HPolytope.isCompact_of_subset (W := P₁.interval.vPolytope) fun x hx => ?_
  have h := (HPolytope.mem_and_iff.mp hx).2
  rw [Interval.hPolytope_exact] at h
  exact Interval.subset_vPolytope _ h

noncomputable def VPolytope.and (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    VPolytope (Vec ℝ n) :=
  if h : (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct.Nonempty then
    (VPolytope.andH P₁ P₂ Aq₁ Aq₂).vPolytope h
  else VPolytope.emptySet _

end CORALean.Real
