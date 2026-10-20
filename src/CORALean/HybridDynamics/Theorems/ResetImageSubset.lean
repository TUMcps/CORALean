module

public import CORALean.HybridDynamics.Theorems.JumpOuter

@[expose] public section

/-!
# The image of a jump, as a set inclusion

`jump_outer` at every point of the intersection at once, which is the form a
chain of steps composes in: a jump's image feeding the next step's `R` needs a
subset, not a per-point membership.

## Inputs
* `e` – transition
* `R` – set holding the state at the jump
* `Rg` – enclosure of the guard intersection

## Hypotheses
* `hinter` – enclosure contains the guard intersection

## Conclusion
* reset image lies in the jump image
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [Real.OfInterval S]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same as an inclusion of the set that leaves, which is the form a chain
of steps composes in. -/
theorem Transition.reset_image_subset (e : Transition G L 𝕋 n) {R Rg : S n}
    (hinter : construct R ∩ construct e.guard ⊆ construct Rg) :
    e.reset '' (construct R ∩ construct e.guard) ⊆ construct (e.jump Rg) := by
  rintro _ ⟨z, ⟨hz, hguard⟩, rfl⟩
  exact e.jump_outer hinter hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
