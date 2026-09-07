import CORALean.ContSet.Conversion.Real.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.VPolytope.Real.Operations.AndH

/-!
# `VPolytope.andH` is compact

The halfspace description sits inside one operand's own box, which a vertex
description already knows is compact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.andH_isCompact (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    IsCompact (VPolytope.andH P₁ P₂ Aq₁ Aq₂).construct := by
  refine HPolytope.isCompact_of_contains (W := P₁.interval.vPolytope) fun x hx => ?_
  have h := (HPolytope.mem_and_iff.mp hx).2
  rw [Interval.hPolytope_exact] at h
  exact Interval.vPolytope_contains _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
