module

public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# Vertices to halfspaces, over a floating-point scalar — the construction

`VPolytope.hPolytope` is the construction; `VPolytope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.hPolytope (P : VPolytope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => P.boundDot (Aq i) fun _ => rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
