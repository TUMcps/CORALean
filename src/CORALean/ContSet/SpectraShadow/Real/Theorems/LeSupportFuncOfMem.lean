import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

/-!
# `SpectraShadow.le_supportFunc_of_mem`

Every point of the set is below the support function: it is a supremum.
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

theorem SpectraShadow.le_supportFunc_of_mem (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) {x : α}
    (hx : x ∈ S.construct) : ((c x : ℝ) : EReal) ≤ S.supportFunc c :=
  le_iSup₂ (f := fun x (_ : x ∈ S.construct) => ((c x : ℝ) : EReal)) x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
