module

public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat

@[expose] public section

/-!
# An order `reachOrderFloat` returns is admissible, and at least the one asked

`MatExp.admissibleOrder_spec` at the norm bound `reachOrderFloat` searches with,
which is the one `OrderAdmissibleFloat` names; the search starts at `max η 2`,
so the order is at least `2` and at least `η`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachOrderFloat_spec {sys : LinearSys 𝕋 n} {tLo tHi : 𝕋} {η : ℕ} :
    ∀ η' ∈ sys.reachOrderFloat tLo tHi η,
      sys.OrderAdmissibleFloat tLo tHi η' ∧ η ≤ η' := by
  intro η' (h : sys.reachOrderFloat tLo tHi η = some η')
  obtain ⟨hε, hle⟩ := MatExp.admissibleOrder_spec _ h
  -- the search starts at `max η 2`, which bounds both floors
  exact ⟨⟨le_trans (le_max_right η 2) hle, hε⟩, le_trans (le_max_left η 2) hle⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
