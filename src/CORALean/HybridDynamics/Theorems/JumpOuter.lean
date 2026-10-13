import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.HybridDynamics.Operations.Jump

/-!
# `Transition.jump` contains the states that leave through the transition

The one step a hybrid analysis takes at a jump: from an enclosure of the states
present when the guard is met, an enclosure of the states just after the reset.
Guard intersection first, reset second.

The intersection arrives as the hypothesis `hinter` rather than as a call, and
that is the deliberate half of this file: the `Intersection` class exists, but
not every representation instantiates it, so this stays generic over `hinter`
rather than calling it. `JumpIntersectionOuter` is the case where an instance
discharges it; `JumpOuterConZonotope`, where a representation with neither
gives up nothing. That bargain is also what lets the guard keep its own
representation `G`: `hinter` is an inclusion of *sets*, so `ContSet` is all
this theorem asks of `G` (#39).

Only *soundness* is at stake: `hinter` may be satisfied by the incoming set
itself, ignoring the guard entirely, and the step stays correct while losing
everything the guard would have removed — hence an exact `intersection` pays.
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
