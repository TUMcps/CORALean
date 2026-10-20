module

public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.Interval.Real.Theorems.MemPoint
public import CORALean.HybridDynamics.Operations.Jump

@[expose] public section

/-!
# `Transition.jump` contains the states that leave through the transition

The one step a hybrid analysis takes at a jump: from an enclosure of the states present when the
guard is met, an enclosure of the states just after the reset; guard intersection first, reset
second. The intersection arrives as the hypothesis `hinter` rather than as a call: not every
representation instantiates `Intersection`. `JumpIntersectionOuter` is the case where an instance
discharges it. That bargain lets the guard keep its own representation `G`: `hinter` is an
inclusion of sets, so `ContSet` is all this theorem asks of `G` (#39). Only soundness is at stake:
`hinter` may be satisfied by the incoming set itself, losing everything the guard would remove.

## Inputs
* `e` – transition
* `R` – set holding the state at the jump
* `Rg` – enclosure of the guard intersection
* `z` – state at the jump

## Hypotheses
* `hinter` – enclosure contains the guard intersection
* `hz` – state lies in the reach set
* `hguard` – state lies in the guard

## Conclusion
* reset image lies in the jump image
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [Real.OfInterval S]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump, `Rg` its intersection with
the guard; the reset image then lands in `jump Rg`. -/
theorem Transition.jump_outer (e : Transition G L 𝕋 n) {R Rg : S n}
    (hinter : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ n}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump Rg) := by -- --- PROOF ---
  show toRealMat e.W *ᵥ z + toRealVec e.w ∈ construct (e.jump Rg)
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer e.W Rg
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hinter ⟨hz, hguard⟩))))
    (ofInterval_outer _ (Real.Interval.mem_point (toRealVec e.w))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
