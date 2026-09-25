import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat

/-!
# An order `reachOrderFloat` returns is admissible, and at least the one asked

`MatExp.admissibleOrder_spec` at the norm bound `reachOrderFloat` searches with,
which is the one `OrderAdmissibleFloat` names; the search starts at `max η 2`,
so the order is at least `2` and at least `η`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachOrderFloat_spec {sys : LinearSys 𝕋 n} {tLo tHi : 𝕋} {η η' : ℕ}
    (h : sys.reachOrderFloat tLo tHi η = some η') :
    sys.OrderAdmissibleFloat tLo tHi η' ∧ η ≤ η' := by
  obtain ⟨hε, hle⟩ := MatExp.admissibleOrder_spec h
  -- the search starts at `max η 2`, which bounds both floors
  exact ⟨⟨le_trans (le_max_right η 2) hle, hε⟩, le_trans (le_max_left η 2) hle⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
