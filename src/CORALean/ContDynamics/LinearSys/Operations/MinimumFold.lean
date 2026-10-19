module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The least of a nonempty family, exactly

`minimumFold f` is the least of `f 0, …, f k`, by the exact `minimum`, with no `zero` above the
entries (see `maximumFold`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least entry, right-nested. -/
def LinearSys.minimumFold : {k : ℕ} → (Fin (k + 1) → 𝕋) → 𝕋
  | 0, f => f 0
  | _ + 1, f => minimum (f 0) (LinearSys.minimumFold fun i => f i.succ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
