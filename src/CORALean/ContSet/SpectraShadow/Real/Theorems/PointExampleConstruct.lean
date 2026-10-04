import CORALean.ContSet.SpectraShadow.Real.Operations.PointExample
import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiOfAZero

/-!
# `SpectraShadow.pointExample_construct`

The point example denotes `{0}`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.pointExample_construct :
    SpectraShadow.pointExample.construct = {0} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, -, rfl⟩
    simp [SpectraShadow.pointExample]
  · -- the zero coefficient is feasible: the inequality is `1 ⪰ 0`
    rintro rfl
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [SpectraShadow.lmi_of_A_zero _ _ fun _ => Or.inl rfl]
      exact Matrix.PosSemidef.one
    · simp [SpectraShadow.pointExample]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
