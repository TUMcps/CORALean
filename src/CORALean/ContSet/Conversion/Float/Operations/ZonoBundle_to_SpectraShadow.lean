module

public import CORALean.ContSet.SpectraShadow.Float.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
public import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# A zonotope bundle as a spectrahedral shadow, over a floating-point scalar — the construction

`ZonoBundle.spectraShadow` is the construction; `ZonoBundle_to_SpectraShadow` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.spectraShadow (zB : ZonoBundle (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  match List.ofFn fun i => Zonotope.spectraShadow (zB.Z i) with
  | [] => SpectraShadow.Inf n                    -- no member: the whole space
  | S :: Ss => Ss.foldl SpectraShadow.inter S    -- `and_` of the members, in order

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
