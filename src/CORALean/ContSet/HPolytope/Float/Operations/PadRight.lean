module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.padRight`

The mirror of `padLeft`, with the new coordinates padded in front.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

-- the mirror, with the new coordinates padded in front
def HPolytope.padRight (n₁ : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n₂)) : HPolytope 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  m := P.m
  A := fun i => Fin.append (fun _ => FloatOps.zero) (P.A i)
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (fun _ => FloatOps.zero) (P.Ae i)
  be := P.be
  I_error := ⟨Fin.append (fun _ => FloatOps.zero) P.I_error.inf,
    Fin.append (fun _ => FloatOps.zero) P.I_error.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
