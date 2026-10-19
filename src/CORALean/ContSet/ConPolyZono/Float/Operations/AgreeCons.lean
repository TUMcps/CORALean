module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.agreeCons` over a floating-point scalar

`Real.ConPolyZono.agreeCons` at the stored floats: the rows of `intersectionDep` pinning the two
points together, each held to its interval `intersectionAgree`, the lower end as the right-hand
side and the width above it, rounded up, as the slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One equation per coordinate, met to within its interval's width. -/
def ConPolyZono.agreeCons (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    PolyLevelSet 𝕋 (cPZ₁.p + cPZ₂.p) :=
  ⟨n, cPZ₁.h + cPZ₂.h, fun i => ConPolyZono.agreeRow cPZ₁ cPZ₂ i,
    Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E, (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf,
    fun i => subUp ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup i)
      ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf i), fun _ => .eq⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
