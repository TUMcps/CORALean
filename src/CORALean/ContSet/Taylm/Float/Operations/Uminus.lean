import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.uminus`

Exact: negation is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.uminus (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  ⟨T.terms.map fun a => (neg a.1, a.2), neg T.remSup, neg T.remInf, T.maxOrder⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
