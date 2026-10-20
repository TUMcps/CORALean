module

public import CORALean.HybridDynamics.Operations.TransitionConvGuard
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionExact

@[expose] public section

/-!
# `Transition.convGuard` is exactly guard and invariant, for error-free polytopes

When the guard's and the invariant's error boxes are both certified to be the origin, as for
every polytope built by a constructor, the new guard denotes the intersection of the old one and
the invariant, with equality: the rows are only stacked (`HPolytope.intersection_exact`). The
reset and the target are untouched. For polytopes with an error box,
`Transition.convGuard_guard_outer` still holds.

## Inputs
* `e` – transition
* `inv` – invariant polytope

## Hypotheses
* `hg` – guard has no error box
* `hi` – invariant has no error box

## Conclusion
* the new guard is the guard intersected with the invariant
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `construct` of the cut guard is the guard's intersection with the invariant. -/
theorem Transition.convGuard_guard_exact (e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (inv : HPolytope 𝕋 (Vec 𝕋 n)) (hg : e.guard.isErrFree = true) (hi : inv.isErrFree = true) :
    (e.convGuard inv).guard.construct = e.guard.construct ∩ inv.construct :=
  (HPolytope.intersection_exact hg hi).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
