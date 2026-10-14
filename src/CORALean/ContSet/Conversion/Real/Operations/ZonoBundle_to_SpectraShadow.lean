module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
public import CORALean.ContSet.Conversion.Real.Zonotope_to_SpectraShadow
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# A zonotope bundle as a spectrahedral shadow — the construction

`ZonoBundle.spectraShadow` is the construction; `ZonoBundle_to_SpectraShadow` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.spectraShadow (zB : ZonoBundle (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  match List.ofFn fun i => (zB.Z i).spectraShadow with
  | [] => SpectraShadow.Inf n                    -- no member: the whole space
  | S :: Ss => Ss.foldl SpectraShadow.inter S    -- `and_` of the members, in order

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
