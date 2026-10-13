module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Origin

@[expose] public section

/-!
# `ZonoBundle.origin`, over a floating-point scalar

A bundle of the one zonotope `Zonotope.origin`, as in CORA.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.origin (n : ℕ) : ZonoBundle (Vec 𝕋 n) := ⟨1, fun _ => Zonotope.origin n⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
