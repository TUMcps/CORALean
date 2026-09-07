import CORALean.ContSet.ConZonotope.Real.Theorems.AndExact
import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# The jump step at a constrained zonotope, with nothing assumed

`JumpOuter`'s hypothesis is what a representation with an exact intersection
supplies, and here it is supplied: `ConZonotope.and_exact` is an equality, so
`hand` holds with no loss at all and the step has no side condition left.

This is what says the interface choice in `JumpOuter` costs nothing. It is also
the only place in this directory that names a representation, and it names one
for the reason the rest of `ContDynamics` does — to record what is left once a
representation that does have the property is substituted in.

Convex only, which a constrained zonotope is. A non-convex guard is
`ConPolyZono.and`, equally exact, and reaches this theorem as soon as
`OfInterval` covers that representation; nothing here would change.

Guard and state are the same representation here because `and` is what supplies
`hand`. `JumpOuter` itself keeps them apart, `hand` being an inclusion (#39).
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {L : Type} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The guard intersection computed rather than assumed. -/
theorem Transition.jump_outer_conZonotope (e : Transition 𝒞 L 𝕋 n)
    {R : ConZonotope (Vec ℝ n)} {z : Vec ℝ n} (hz : z ∈ construct R)
    (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump (S := 𝒞) (R.and e.guard)) :=
  e.jump_outer (ConZonotope.and_exact R e.guard).subset hz hguard

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
