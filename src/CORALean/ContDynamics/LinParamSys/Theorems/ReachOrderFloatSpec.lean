import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat

/-!
# An order `reachOrderFloat` returns is admissible, and at least the one asked

`MatExp.admissibleOrder_spec` at the norm bound `reachOrderFloat` searches with,
which is the one `OrderAdmissibleFloat` names, as for `LinearSys`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachOrderFloat_spec
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {tLo tHi : 𝕋} {η η' : ℕ}
    (h : sys.reachOrderFloat tLo tHi η = some η') :
    sys.OrderAdmissibleFloat tLo tHi η' ∧ η ≤ η' := by
  obtain ⟨hε, hle⟩ := MatExp.admissibleOrder_spec h
  -- the search starts at `max η 2`, which bounds both floors
  exact ⟨⟨le_trans (le_max_right η 2) hle, hε⟩, le_trans (le_max_left η 2) hle⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
