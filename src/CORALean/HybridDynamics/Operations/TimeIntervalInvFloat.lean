module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.HybridDynamics.Operations.TimeIntervalFloat
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Location.timeIntervalInvFloat`

`Location.timeIntervalInv` at a float zonotope. The float zonotope has no `Intersection`
instance, so the cut goes through a box: the stay enclosure plus the input contribution `Ud` is
boxed by `Zonotope.interval`, cut to the invariant's rows by `HPolytope.contractBox` and read back
as a zonotope. The invariant is a float halfspace description in its own family, as a guard is
(#39). The box is coarser than the zonotope wherever no row cuts, so this is the cut a guard test
wants, not a set to keep propagating.

## Inputs
* `ℓ` – float location
* `r` – time step
* `η` – Taylor order
* `X₀` – initial zonotope
* `Ud` – input contribution

## Output
* float zonotope cut by the invariant
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stay enclosure over `X₀` and `Ud`, boxed and cut down to the location's invariant. -/
def Location.timeIntervalInvFloat
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (r : 𝕋) (η : ℕ) (X₀ Ud : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  (ℓ.inv.contractBox (ℓ.timeIntervalFloat r η X₀ ⊞ Ud).interval).zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
