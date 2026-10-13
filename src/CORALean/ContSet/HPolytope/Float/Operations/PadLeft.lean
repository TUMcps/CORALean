import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.padLeft`

The same constraints on a wider coefficient space, the new coordinates padded
with zeros on the right so they answer to nothing. Exact: padding copies
floats and computes none.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.padLeft (P : HPolytope 𝕋 (Vec 𝕋 n₁)) (n₂ : ℕ) : HPolytope 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  m := P.m
  A := fun i => Fin.append (P.A i) fun _ => FloatOps.zero
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (P.Ae i) fun _ => FloatOps.zero
  be := P.be

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
