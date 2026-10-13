module

public import CORALean.ContSet.Taylm.Float.Operations.Sum

@[expose] public section

/-!
# `Taylm.trace`, over a floating-point scalar

The sum of the diagonal, `Taylm.sum` of `A i i`; see the exact layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.trace {k : ℕ} (A : Fin k → Fin k → Taylm 𝕋 n) : Taylm 𝕋 n :=
  Taylm.sum fun i => A i i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
