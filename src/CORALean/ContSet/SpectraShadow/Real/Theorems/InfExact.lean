import CORALean.ContSet.SpectraShadow.Real.Operations.Inf
import CORALean.ContSet.SpectraShadow.Real.Theorems.A0AddSumEq

/-!
# `SpectraShadow.Inf` denotes everything


-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.Inf_exact (n : ℕ) :
    (SpectraShadow.Inf n).construct = Set.univ := by -- --- PROOF ---
  ext x
  simp only [SpectraShadow.construct, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  -- the coefficients are `x` itself, read through the unit vectors
  refine ⟨fun i => x ⟨i.1, i.2⟩, ?_, ?_⟩
  · rw [SpectraShadow.A₀_add_sum_eq (SpectraShadow.Inf n) _ (fun _ => rfl)]
    have h1 : (!![1] : Mat ℝ 1 1) = 1 := by
      ext a b; fin_cases a; fin_cases b; rfl
    show (!![1] : Mat ℝ 1 1).PosSemidef
    rw [h1]
    exact Matrix.PosSemidef.one
  · ext (j : Fin n)
    simp [SpectraShadow.Inf, Finset.sum_apply, Pi.single_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
