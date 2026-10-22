module

public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ContSet.ContSet
public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.jumpIntersectionOfPoint`

`aux_jumpOfPoint` with the guard intersection computed rather than assumed, exactly
as `jumpIntersection` is `jump` with it. At `ConPolyZono`, whose `Intersection`
is exact and whose only offset ask is `OfPoint`, this is what cuts a non-convex
reachable set by a guard exactly — the payoff `OfPoint` exists for.

As at `jumpIntersection`, `Intersection.intersection` is homogeneous, so the
guard is asked to be in the state's own family here and nowhere else (#39).

## Inputs
* `e` – transition
* `R` – reach set

## Output
* image of the guard intersection under the reset
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes OfPoint

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {L : Type} {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open CORALean.Real
variable {G : ℕ → Type} {L : Type} {n : ℕ}

def Transition.aux_jumpOfPoint (e : Transition G L 𝕋 n) (Rg : S n) : S n :=
  plus (mtimes e.W Rg) (ofPoint (toRealVec e.w))


/-- Anonymous, its content being that it elaborates (#38): `ConPolyZono` has no
`OfInterval` instance, so `jump` is unavailable to it, and `aux_jumpOfPoint`
above is what fills the gap. -/
example (e : Transition 𝒞𝒫𝒵 L ℝ n) (Rg : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  e.aux_jumpOfPoint (S := 𝒞𝒫𝒵) Rg

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_jumpOfPoint`, with the incoming enclosure cut to the guard by `Intersection.intersection`
first. -/
def Transition.jumpIntersectionOfPoint [∀ n, Intersection (S n) (Vec ℝ n)]
    (e : Transition S L 𝕋 n) (R : S n) : S n :=
  e.aux_jumpOfPoint (Intersection.intersection R e.guard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
