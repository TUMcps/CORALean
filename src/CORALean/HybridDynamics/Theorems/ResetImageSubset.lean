import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# The image of a jump, as a set inclusion

`jump_outer` at every point of the intersection at once, which is the form a
chain of steps composes in: a jump's image feeding the next step's `R` needs a
subset, not a per-point membership.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same as an inclusion of the set that leaves, which is the form a chain
of steps composes in. -/
theorem Transition.reset_image_subset (e : Transition S L 𝕋 n) {R Rg : S n}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) :
    e.reset '' (construct R ∩ construct e.guard) ⊆ construct (e.jump Rg) := by
  rintro _ ⟨z, ⟨hz, hguard⟩, rfl⟩
  exact e.jump_outer hand hz hguard

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
