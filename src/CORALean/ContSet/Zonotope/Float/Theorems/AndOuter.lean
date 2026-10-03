import CORALean.ContSet.Zonotope.Float.Operations.And
import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter

/-!
# The float `'conZonotope'` intersection of zonotopes encloses the intersection

Zonotope into constrained zonotope (`conZonotope_contains`), the outer float intersection
(`ConZonotope.intersection_outer`), and the constraints forgotten (`zonotope_contains`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.and_outer (Z S : Zonotope 𝕋 n) :
    Z.construct ∩ S.construct ⊆ (Z.and_ S).construct :=
  fun _ hx => ConZonotope.zonotope_contains _
    (ConZonotope.intersection_outer _ _
      ⟨Z.conZonotope_contains hx.1, S.conZonotope_contains hx.2⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
