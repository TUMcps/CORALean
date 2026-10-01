import CORALean.ContSet.Fullspace.Real.Operations.SupportFunc
import CORALean.ContSet.Fullspace.Real.Fullspace
import CORALean.ContSet.ContSet.ContSet

/-!
# `Fullspace.supportFunc` is the supremum

`Inf` is the supremum of a nonzero functional over the whole space in `EReal`: scaling a point
where it is nonzero reaches any bound.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.supportFunc_eq (F : Fullspace n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    F.supportFunc c = ⨆ x ∈ F.construct, ((c x : ℝ) : EReal) := by -- --- PROOF ---
  by_cases hc : c = 0
  · subst hc
    change _ = ⨆ x ∈ (Set.univ : Set (Vec ℝ n)), (((0 : Vec ℝ n →ₗ[ℝ] ℝ) x : ℝ) : EReal)
    simp [Fullspace.supportFunc]
  · rw [Fullspace.supportFunc, if_neg hc]
    symm
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (LinearMap.ext h)
    have hp : c (((y + 1) / c x₀) • x₀) = y + 1 := by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx₀]
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (show y < y + 1 by linarith)) ?_
    rw [← hp]
    exact le_iSup₂ (f := fun x (_ : x ∈ F.construct) => ((c x : ℝ) : EReal)) _ (Set.mem_univ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
