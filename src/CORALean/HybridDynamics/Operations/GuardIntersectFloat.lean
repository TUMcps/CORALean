import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
import CORALean.ContSet.Interval.Float.Operations.Or
import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet
import CORALean.HybridDynamics.Definitions.Location

/-!
# `Location.guardIntersectFloat`

CORA's `guardIntersect` with its `'box'` method, at float zonotopes: every
time-interval set of a stay is boxed, cut to the location's invariant and then
to the guard by `HPolytope.contractBox`, and the cuts that may be non-empty are
joined into their box hull, the one set the reset is applied to.

`none` when every cut is certified empty by `representsa_emptySet`: the stay
never meets the guard, and the transition is not taken. A cut that cannot be
certified empty is kept, which is the sound direction. Cutting by the invariant
first is CORA's too; a jump happens at a state the stay reaches, which lies in
the invariant.
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

/-- The box hull of the time-interval sets `Rs` cut to the invariant and to `guard`,
or `none` when no cut can meet the guard. -/
def Location.guardIntersectFloat
    (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (guard : HPolytope 𝕋 (Vec 𝕋 n)) (Rs : List (Zonotope (Vec 𝕋 n))) : Option
    (Interval (Vec 𝕋 n)) :=
  let cut := Rs.map fun R => guard.contractBox (ℓ.inv.contractBox R.interval)  -- R ∩ inv ∩ guard
  match cut.filter fun I => !I.representsa_emptySet with   -- those that may be non-empty
  | [] => none                                              -- the guard is never met
  | I :: Is => some (Is.foldl Interval.or I).materialise    -- their box hull

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
