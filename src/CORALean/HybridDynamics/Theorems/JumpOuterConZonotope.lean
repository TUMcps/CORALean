module

public import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.HybridDynamics.Theorems.JumpOuter

@[expose] public section

/-!
# The jump step at a constrained zonotope, with nothing assumed

`JumpOuter`'s hypothesis is what a representation with an exact intersection supplies, and here it
is supplied: `ConZonotope.intersection_exact` is an equality, so `hinter` holds with no loss and
the step has no side condition left. This is what says the interface choice in `JumpOuter` costs
nothing. Convex only, which a constrained zonotope is; a non-convex guard is
`ConPolyZono.intersection`, equally exact. Guard and state are the same representation here because
`intersection` is what supplies `hinter`; `JumpOuter` itself keeps them apart (#39).

## Inputs
* `e` – transition
* `R` – constrained zonotope holding the state at the jump
* `z` – state at the jump

## Hypotheses
* `hz` – state lies in the reach set
* `hguard` – state lies in the guard

## Conclusion
* reset image lies in the jump image
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {L : Type} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The guard intersection computed rather than assumed. -/
theorem Transition.jump_outer_conZonotope (e : Transition 𝒞 L 𝕋 n)
    {R : Real.ConZonotope (Vec ℝ n)} {z : Vec ℝ n} (hz : z ∈ construct R)
    (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump (S := 𝒞) (R.intersection e.guard)) :=
  e.jump_outer (Real.ConZonotope.intersection_exact R e.guard).subset hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
