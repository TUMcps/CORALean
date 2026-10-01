import CORALean.ContSet.SpectraShadow.Real.Operations.Empty
import CORALean.ContSet.SpectraShadow.Real.Theorems.A0AddSumEq

/-!
# `SpectraShadow.empty` denotes the empty set


-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.empty_exact (n : ℕ) :
    (SpectraShadow.empty n).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [SpectraShadow.construct, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, hβ, -⟩
  -- the inequality is `-1 ⪰ 0`, whatever `β` is
  rw [SpectraShadow.A₀_add_sum_eq _ β (fun _ => rfl)] at hβ
  have h := Matrix.PosSemidef.diag_nonneg (i := (0 : Fin 1))
    (show (!![-1] : Mat ℝ 1 1).PosSemidef from hβ)
  norm_num at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
