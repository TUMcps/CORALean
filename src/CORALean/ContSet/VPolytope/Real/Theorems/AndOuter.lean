import CORALean.ContSet.VPolytope.Real.Operations.And
import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet

/-!
# `VPolytope.and` contains the intersection

Both operands land in their own halfspace descriptions, intersection of
halfspace descriptions is exact, and vertex enumeration puts the result back —
or, when nothing is left, the empty vertex list already contains nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.and_outer (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.and P₂ Aq₁ Aq₂).construct := by
  have hsub : P₁.construct ∩ P₂.construct ⊆ (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct := by
    rintro x ⟨hx₁, hx₂⟩
    refine HPolytope.mem_and_iff.mpr ⟨HPolytope.mem_and_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · exact P₁.subset_hPolytope Aq₁ hx₁
    · exact P₂.subset_hPolytope Aq₂ hx₂
    · rw [Interval.hPolytope_exact]
      exact P₁.interval_outer hx₁
  -- empty or not: an empty halfspace description leaves nothing to enumerate
  by_cases h : (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct.Nonempty
  · have he : P₁.and P₂ Aq₁ Aq₂ = (VPolytope.andH P₁ P₂ Aq₁ Aq₂).vPolytope h := dif_pos h
    rw [he]
    exact subset_trans hsub
      (HPolytope.subset_vPolytope _ (VPolytope.andH_isCompact P₁ P₂ Aq₁ Aq₂) h)
  · have he : P₁.and P₂ Aq₁ Aq₂ = VPolytope.emptySet (Vec ℝ n) := dif_neg h
    rw [he, VPolytope.construct_emptySet]
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hsub
    exact hsub

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
