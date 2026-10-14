module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A box as an ellipsoid, over a floating-point scalar
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One generator per coordinate, the box's own radius scaled by the proposed
`√n` and rounded up. -/
def Interval.ellipsoidG (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n n :=
  diagonalBlock fun i => mulUp σ (I.radiusFrom i)

def Interval.ellipsoid (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  k := n
  c := I.center
  G := I.ellipsoidG σ
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
