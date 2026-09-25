import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AccurateOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.WindowOrderFloat

/-!
# An order `windowOrderFloat` returns is admissible at the window

`MatExp.accurateOrder_spec` at the norm bound of `[tLo, tHi] · A`, the one
`OrderAdmissibleFloat` names; the search starts at `max η 2`. The tolerance the
order also meets is precision, and not needed here.
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

theorem LinearSys.windowOrderFloat_spec {sys : LinearSys 𝕋 n} {Δt tLo tHi : 𝕋} {η ηk : ℕ}
    (h : sys.windowOrderFloat Δt tLo tHi η = some ηk) :
    sys.OrderAdmissibleFloat tLo tHi ηk ∧ η ≤ ηk := by
  obtain ⟨hε, hle, -⟩ := MatExp.accurateOrder_spec h
  -- the search starts at `max η 2`, which bounds both floors
  exact ⟨⟨le_trans (le_max_right η 2) hle, hε⟩, le_trans (le_max_left η 2) hle⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
