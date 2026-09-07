import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.HybridDynamics.Operations.Jump

/-!
# `Transition.jump` contains the states that leave through the transition

The one step a hybrid analysis takes at a jump: from an enclosure of the states
present when the guard is met, an enclosure of the states just after the reset.
Guard intersection first, reset second.

The intersection arrives as the hypothesis `hand` rather than as a call, and that
is the deliberate half of this file: the `And` class exists, but not every
representation instantiates it, so this stays generic over `hand`, a
`SupportBound` bargain, rather than calling `And.and` outright. `JumpAndOuter`
is the case where an `And` instance discharges it; `JumpOuterConZonotope`
discharges it with nothing given away at a representation with neither.

Only *soundness* is at stake. `hand` may be satisfied by the incoming set itself,
ignoring the guard entirely, and the step stays correct while losing everything
the guard would have removed — which is why a representation with an exact `and`
is worth having.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump, `Rg` its intersection with
the guard; the reset image then lands in `jump Rg`. -/
theorem Transition.jump_outer (e : Transition S L 𝕋 n) {R Rg : S n}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ n}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump Rg) := by -- --- PROOF ---
  show toRealMat e.W *ᵥ z + toRealVec e.w ∈ construct (e.jump Rg)
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer e.W Rg
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hand ⟨hz, hguard⟩))))
    (ofInterval_outer _ (Interval.mem_point (toRealVec e.w))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
