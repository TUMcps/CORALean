module

public import CORALean.ContSet.HPolytope.Float.Operations.InHalfspace
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Instances

@[expose] public section

/-!
# `Location.guardOrientFloat?`: the guard hyperplane's normal out of the invariant

CORA's `checkFlow` (`aux_adaptGuard`) turns the normal of the guard hyperplane `n·x = γ` so that it
points out of the invariant, deciding by whether the center of the first reach set lies in the
invariant and on which side of the hyperplane. Here the side is read off the invariant: if one of
its rows is `n` with a right-hand side certified at most `γ`, the normal is `n`; if one is `-n`
with a right-hand side certified at most `-γ`, it is `-n`; otherwise there is no certified side
(`HPolytope.inHalfspace`, sound by `HPolytope.inHalfspace_sound`). The normal is not normalised:
a unit normal, as CORA's, is the caller's, and the projection is onto `{x | n·x = γ}` only for one.

## Inputs
* `ℓ` – location
* `nv` – normal of the guard hyperplane
* `γ` – offset of the guard hyperplane

## Output
* the normal and offset with the invariant in `c·x ≤ d`, none when no row certifies a side
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The oriented normal and offset of the hyperplane `nv·x = γ` with the invariant inside
`c·x ≤ d`, if a row of the invariant certifies it. -/
def Location.guardOrientFloat?
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (nv : Vec 𝕋 n) (γ : 𝕋) :
    Option (Vec 𝕋 n × 𝕋) :=
  if ℓ.inv.inHalfspace nv γ then some (nv, γ)
  else if ℓ.inv.inHalfspace (-nv) (-γ) then some (-nv, -γ)
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
