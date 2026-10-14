module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# A zonotope as a constrained one, over a floating-point scalar — the construction

`Zonotope.conZonotope` is the construction; `Zonotope_to_ConZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.conZonotope (Z : Zonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  ⟨Z.h, Z.c, Z.G, HPolytope.fullspace 𝕋 Z.h, Z.I_error⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
