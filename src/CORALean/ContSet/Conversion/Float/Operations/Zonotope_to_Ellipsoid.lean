module

public import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A zonotope as an ellipsoid, over a floating-point scalar — the construction

`Zonotope.ellipsoidG`, `Zonotope.ellipsoidGap`, `Zonotope.ellipsoidSlack` and `Zonotope.ellipsoid`
are the constructions; `Zonotope_to_Ellipsoid` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators scaled by the proposed `√h`, rounded up. -/
def Zonotope.ellipsoidG (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n Z.h :=
  fun i j => mulUp σ (Z.G j i)

/-- The width of each scaled generator's rounding bracket. -/
def Zonotope.ellipsoidGap (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n Z.h :=
  fun i j => subUp (mulUp σ (Z.G j i)) (mulDown σ (Z.G j i))

/-- What the rounding of the generators can move a point by, rounded up. -/
def Zonotope.ellipsoidSlack (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Vec 𝕋 n :=
  fun i => divUp (radius (Z.ellipsoidGap σ) i) σ

def Zonotope.ellipsoid (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  k := Z.h
  c := Z.c
  G := Z.ellipsoidG σ
  I_error := ⟨fun i => subDown (Z.I_error.inf i) (Z.ellipsoidSlack σ i),
          fun i => addUp (Z.I_error.sup i) (Z.ellipsoidSlack σ i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
