import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPointCora
import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleNotMem

/-!
# `SpectraShadow.containsPointCora_line`

`contains_` on a numeric operand: `(1, 0)` is not on the line `{(t, t)}`, so `c + G β = p` is
infeasible and CORA, reading the solver's status `1` as an internal error, answers `true`. Read from
the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.containsPointCora_line (tol : ℝ) :
    SpectraShadow.lineExample.containsPointCora (Pi.single 0 1) tol
      ∧ (Pi.single 0 1 : Vec ℝ 2) ∉ SpectraShadow.lineExample.construct := by
  refine ⟨Or.inl SpectraShadow.lineExample_not_mem, ?_⟩
  rintro ⟨β, -, hx⟩
  exact SpectraShadow.lineExample_not_mem ⟨β, hx.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
