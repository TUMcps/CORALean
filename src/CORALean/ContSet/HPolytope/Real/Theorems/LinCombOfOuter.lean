module

public import CORALean.ContSet.HPolytope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# The certified convex combination encloses

The same line as `plusOf_outer` at a different composition of certificates:
`ofBounds` says exactly what the bounds handed to it say, and the bounds were
composed to speak about the segments between the two sets.

The enclosure claimed by [1, Eq. 31].

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


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
