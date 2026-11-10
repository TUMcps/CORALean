module

public import CORALean.ContSet.ConZonotope.Float.Definitions.BoxMethod
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalCert

@[expose] public section

/-!
# The box of a constrained zonotope, by a chosen method, over a floating-point scalar

The box of the method `ConZonotope.BoxMethod` names: `intervalTight`, `intervalCert` or the
intersection of the two.

## Inputs
* `m` – method of the box
* `cZ` – float constrained zonotope

## Output
* box holding the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box of the method. -/
def ConZonotope.box [ToRat 𝕋] (m : ConZonotope.BoxMethod) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Interval (Vec 𝕋 n) :=
  match m with
  | .fm k => cZ.intervalTight k
  | .cert => cZ.intervalCert
  | .both k => cZ.intervalCertTight k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
