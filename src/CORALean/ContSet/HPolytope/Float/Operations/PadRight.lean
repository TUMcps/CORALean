import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.padRight`

The mirror of `padLeft`, with the new coordinates padded in front.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}

-- the mirror, with the new coordinates padded in front
def HPolytope.padRight (n₁ : ℕ) (P : HPolytope 𝕋 n₂) : HPolytope 𝕋 (n₁ + n₂) where
  m := P.m
  A := fun i => Fin.append (fun _ => FloatOps.zero) (P.A i)
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (fun _ => FloatOps.zero) (P.Ae i)
  be := P.be

end CORALean.Float
