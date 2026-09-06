import CORALean.ContSet.HPolytope.Real.Operations.LinComb
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds

/-!
# The certified convex combination encloses

The same line as `plusOf_outer` at a different composition of certificates:
`ofBounds` says exactly what the bounds handed to it say, and the bounds were
composed to speak about the segments between the two sets.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]
variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.linCombOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    segments P₁.construct P₂.construct ⊆ (HPolytope.linCombOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
