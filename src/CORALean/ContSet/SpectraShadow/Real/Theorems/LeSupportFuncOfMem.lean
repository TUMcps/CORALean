module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

@[expose] public section

/-!
# `SpectraShadow.le_supportFunc_of_mem`

Every point of the set is below the support function: it is a supremum.
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

theorem SpectraShadow.le_supportFunc_of_mem (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) {x : α}
    (hx : x ∈ S.construct) : ((c x : ℝ) : EReal) ≤ S.supportFunc c :=
  le_iSup₂ (f := fun x (_ : x ∈ S.construct) => ((c x : ℝ) : EReal)) x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
