module

public import CORALean.HybridDynamics.Operations.LocationGuardOrientFloat
public import CORALean.HybridDynamics.Operations.CheckFlowFloat

@[expose] public section

/-!
# `Location.queueSetsFloat`: the sets of a crossing that `checkFlow` keeps

In CORA's `guardIntersect.m`, a group of reach sets at a hyperplane guard goes through `checkFlow`
before the intersection, which keeps the sets whose flow may point out through the guard; the
group is dropped when none is kept. The normal is turned out of the invariant
(`Location.guardOrientFloat?`, sound by `Location.guardOrientFloat?_sound`); without a
certified side every set is kept. With `checkFlow` off,
all sets are kept.

## Inputs
* `ℓ` – location
* `chk` – whether to apply `checkFlow`
* `nv` – normal of the guard hyperplane
* `γ` – offset of the guard hyperplane
* `idxs` – set indices of the group
* `Rs` – sets of the stay

## Output
* the sets of the group that go on to the intersection
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sets of the group `idxs` kept by `checkFlow`, all of them when it is off. -/
def Location.queueSetsFloat
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (chk : Bool) (nv : Vec 𝕋 n)
    (γ : 𝕋) (idxs : List ℕ) (Rs : List (Zonotope (Vec 𝕋 n))) : List (Zonotope (Vec 𝕋 n)) :=
  let sets := idxs.filterMap fun j => Rs[j]?
  match chk, ℓ.guardOrientFloat? nv γ with
  | true, some (c, d) => ℓ.checkFlowFloat c d sets
  | _, _ => sets

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
