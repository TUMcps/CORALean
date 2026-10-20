module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A box as an ellipsoid, over a floating-point scalar

CORA's `ellipsoid(I)` of a box: the shape `diag(σ r)²`, `r` the box's radius and `σ ≥ √n` a
proposed scaling, each entry rounded up, about the box's center.

## Inputs
* `I` – interval
* `σ` – proposed scaling factor

## Output
* diagonal generator from the box radius, rounded up
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The diagonal generator: the box's own radius scaled by the proposed `√n`, rounded up. -/
def Interval.ellipsoidG (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n n :=
  diagonalBlock fun i => mulUp σ (I.radiusFrom i)

def Interval.ellipsoid (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  Q := diagonalBlock fun i => mulUp (I.ellipsoidG σ i i) (I.ellipsoidG σ i i)
  q := I.center
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
