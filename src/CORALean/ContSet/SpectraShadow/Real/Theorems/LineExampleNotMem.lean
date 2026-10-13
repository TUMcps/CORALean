import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleSum

/-!
# `SpectraShadow.lineExample_not_mem`

No coefficient reaches `(1, 0)`: the line example's points are diagonal.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.lineExample_not_mem : ¬ ∃ β : Fin 2 → ℝ,
    SpectraShadow.lineExample.c + ∑ i : Fin 2, β i • SpectraShadow.lineExample.G i
      = (Pi.single 0 1 : Vec ℝ 2) := by -- --- PROOF ---
  rintro ⟨β, hx⟩
  rw [SpectraShadow.lineExample_sum] at hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp at h0 h1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
