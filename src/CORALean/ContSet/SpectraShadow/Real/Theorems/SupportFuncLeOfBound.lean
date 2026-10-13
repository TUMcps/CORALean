import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
import CORALean.Global.LinProg.LinProg

/-!
# `SpectraShadow.supportFunc_le_of_bound`

A certified bound (`SupportBound`) is above the support function.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFunc_le_of_bound (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (u : SupportBound S.construct c) : S.supportFunc c ≤ (u.val : EReal) :=
  iSup₂_le fun x hx => EReal.coe_le_coe_iff.mpr (u.le x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
