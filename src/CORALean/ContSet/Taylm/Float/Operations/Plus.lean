import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.plus`

The term lists side by side, which rounds nothing; only the remainder sum rounds outward.
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

def Taylm.plus (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  ⟨T₁.terms ++ T₂.terms, addDown T₁.remInf T₂.remInf, addUp T₁.remSup T₂.remSup,
    max T₁.maxOrder T₂.maxOrder⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
