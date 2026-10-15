module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.padLeft`

The same constraints on a wider coefficient space, the new coordinates padded
with zeros on the right so they answer to nothing, and the error box padded with the point
`[0, 0]` there. Exact: padding copies floats and computes none.
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

def HPolytope.padLeft (P : HPolytope 𝕋 (Vec 𝕋 n₁)) (n₂ : ℕ) : HPolytope 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  m := P.m
  A := fun i => Fin.append (P.A i) fun _ => FloatOps.zero
  b := P.b
  me := P.me
  Ae := fun i => Fin.append (P.Ae i) fun _ => FloatOps.zero
  be := P.be
  I_error := ⟨Fin.append P.I_error.inf fun _ => FloatOps.zero,
    Fin.append P.I_error.sup fun _ => FloatOps.zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
