module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Location.guardIntersectFloat`

CORA's `guardIntersect` with its `'box'` method, at float zonotopes: every time-interval set of a
stay is boxed, cut to the location's invariant and then to the guard by `HPolytope.contractBox`,
and the cuts that may be non-empty are joined into their box hull, the one set the reset is
applied to. `none` when every cut is certified empty by `representsa_emptySet`; a cut that cannot
be certified empty is kept, the sound direction. Cutting by the invariant first is CORA's too.

## Inputs
* `ℓ` – location
* `guard` – guard polytope
* `Rs` – reach sets of the stay

## Output
* box hull of the cuts, none if all are empty
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
