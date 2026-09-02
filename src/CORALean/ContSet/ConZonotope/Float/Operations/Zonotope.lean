import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# Between a float zonotope and a float constrained one

Forgetting the constraints keeps the centre, the generators and the box exactly
as they were, so neither direction computes anything and neither rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConZonotope.zonotope (C : ConZonotope 𝕋 n) : Zonotope 𝕋 n := ⟨C.h, C.c, C.G, C.E⟩

def Zonotope.conZonotope (Z : Zonotope 𝕋 n) : ConZonotope 𝕋 n :=
  ⟨Z.h, Z.c, Z.G, HPolytope.fullspace 𝕋 Z.h, Z.E⟩

end CORALean.Float
