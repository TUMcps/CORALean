import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFuncCoraAllZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct

/-!
# `SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`

`supportFunc_` and `isBounded` on the point `{0}` (`A₀ = 1`, `A₁ = 0`, `G = 0`): CORA's
`all_Ai_zero` branch returns `+Inf` while the support is `0`. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFuncCoraAllZero_ne_supportFunc :
    SpectraShadow.pointExample.supportFuncCoraAllZero
      ≠ SpectraShadow.pointExample.supportFunc
        (LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ) := by -- --- PROOF ---
  -- CORA: `A₀ = 1 ⪰ 0`, so `+Inf`
  have h1 : SpectraShadow.pointExample.supportFuncCoraAllZero = ⊤ := by
    classical
    simp only [SpectraShadow.supportFuncCoraAllZero, SpectraShadow.pointExample]
    rw [if_pos Matrix.PosSemidef.one]
  -- the set: the support in the one coordinate is `0`
  have h2 : SpectraShadow.pointExample.supportFunc
      (LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ) = 0 := by
    rw [SpectraShadow.supportFunc, SpectraShadow.pointExample_construct]
    simp
  rw [h1, h2]
  exact EReal.top_ne_zero

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
