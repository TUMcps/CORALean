import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleSum
import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiOfAZero

/-!
# `SpectraShadow.lineExample_mem`

Every diagonal point is in the line example: take the coefficient `(t, 0)`, where the
inequality is `I ⪰ 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.lineExample_mem (t : ℝ) :
    (fun _ => t : Vec ℝ 2) ∈ SpectraShadow.lineExample.construct := by -- --- PROOF ---
  refine ⟨fun j : Fin 2 => if j = 0 then t else 0, ?_, ?_⟩
  · -- `A₀ = I` and the second coefficient is `0`, where `A₁ = 0`
    rw [SpectraShadow.lmi_of_A_zero _ _ (fun i => ?_)]
    · exact Matrix.PosSemidef.one
    · fin_cases i
      · exact Or.inr (by simp only [SpectraShadow.lineExample]; exact if_pos rfl)
      · exact Or.inl (if_neg (by decide))
  · exact ((SpectraShadow.lineExample_sum (fun j : Fin 2 => if j = 0 then t else 0)).trans
      (by simp)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
