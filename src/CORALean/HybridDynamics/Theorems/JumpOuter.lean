import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.HybridDynamics.Operations.Jump

/-!
# `Transition.jump` contains the states that leave through the transition

The one step a hybrid analysis takes at a jump: from an enclosure of the states
present when the guard is met, an enclosure of the states just after the reset.
Guard intersection first, reset second.

The intersection arrives as the hypothesis `hand` rather than as a call, and that
is the deliberate half of this file. There is no `And` class — only two
representations implement an intersection — so a theorem intersecting generically
would have to invent the interface. `hand` is the `SupportBound` bargain instead:
the caller brings whatever encloses the intersection together with its proof.
`JumpOuterConZonotope` discharges it with nothing given away.

Only *soundness* is at stake. `hand` may be satisfied by the incoming set itself,
ignoring the guard entirely, and the step stays correct while losing everything
the guard would have removed — which is why a representation with an exact `and`
is worth having.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {L : Type} {n : ℕ}

/-- `R` encloses the state at the moment of the jump, `Rg` its intersection with
the guard; the reset image then lands in `jump Rg`. -/
theorem Transition.jump_outer (e : Transition S L 𝕋 n) {R Rg : S n}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ n}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump Rg) := by
  show toRealMat e.W *ᵥ z + toRealVec e.w ∈ construct (e.jump Rg)
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer e.W Rg
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hand ⟨hz, hguard⟩))))
    (ofInterval_outer _ (Interval.mem_point (toRealVec e.w))))

end CORALean.Real
