module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The largest of a nonempty family, exactly

`maximumFold f` is the greatest of `f 0, …, f k`, by the exact `maximum`. Unlike `maximumOver`, it
has no `zero` below the entries, so a negative maximum stays negative, which a verification
that asks whether every distance is `≤ 0` needs.

## Inputs
* none

## Output
* greatest entry of a nonempty family
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greatest entry, right-nested. -/
def LinearSys.maximumFold : {k : ℕ} → (Fin (k + 1) → 𝕋) → 𝕋
  | 0, f => f 0
  | _ + 1, f => maximum (f 0) (LinearSys.maximumFold fun i => f i.succ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
