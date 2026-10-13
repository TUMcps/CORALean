import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
import CORALean.HybridDynamics.Operations.TimeIntervalStepFloat

/-!
# `Location.timeIntervalStepInvFloat`

`Location.timeIntervalStepInv` at a float zonotope. The float zonotope has no
`Intersection` instance, so the cut goes through a box: the stay enclosure
plus the input contribution `Ud`, as at the exact step, is boxed by
`Zonotope.interval`, cut to the invariant's rows by `HPolytope.contractBox`,
and read back as a zonotope.

The invariant is a float halfspace description, in its own family as a guard
is, rather than in the state's: nothing intersects two zonotopes here (#39).
The box is coarser than the zonotope it came from wherever no row cuts, so
this is the cut a guard test wants, not a set to keep propagating.
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
def Location.timeIntervalStepInvFloat
    (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (r : 𝕋) (η : ℕ) (X₀ Ud : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  (ℓ.inv.contractBox (ℓ.timeIntervalStepFloat r η X₀ ⊞ Ud).interval).zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
