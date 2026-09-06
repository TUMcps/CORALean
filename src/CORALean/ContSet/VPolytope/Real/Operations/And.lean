import CORALean.ContSet.VPolytope.Real.Operations.AndH
import CORALean.ContSet.VPolytope.Real.Operations.AndHIsCompact
import CORALean.ContSet.VPolytope.Real.Operations.EmptySet

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
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.and (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    VPolytope (Vec ℝ n) :=
  if h : (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct.Nonempty then
    (VPolytope.andH P₁ P₂ Aq₁ Aq₂).vPolytope h
  else VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
