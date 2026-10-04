import CORALean.ContSet.SpectraShadow.Real.Operations.SupportBound
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncLeOfBound

/-!
# `SpectraShadow.supportFunc_le_supportBound`

Weak duality: a dual certificate `Y` bounds the support function by `c(c₀) + tr(A₀ Y)`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFunc_le_supportBound (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (Y : Mat ℝ S.k S.k) (hY : Y.PosSemidef) (hc : ∀ i, (S.A i * Y).trace = - c (S.G i)) :
    S.supportFunc c ≤ ((c S.c + (S.A₀ * Y).trace : ℝ) : EReal) :=
  S.supportFunc_le_of_bound c (S.supportBound c Y hY hc)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
