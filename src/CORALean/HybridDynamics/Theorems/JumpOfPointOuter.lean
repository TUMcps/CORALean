module

public import CORALean.HybridDynamics.Operations.JumpOfPoint
public import CORALean.HybridDynamics.Theorems.JumpOuter

@[expose] public section

/-!
# `Transition.jumpOfPoint` contains the states that leave through the transition

`jump_outer`'s guarantee, `hinter` and all, at `ofPoint` in place of whatever
`OfInterval` supplied for the offset — the proof is the same shape, one
membership fact swapped for another.

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
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes OfPoint

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump, `Rg` its intersection with
the guard; the reset image then lands in `jumpOfPoint Rg`. -/
theorem Transition.jumpOfPoint_outer (e : Transition G L 𝕋 n) {R Rg : S n}
    (hinter : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ n}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) : -- --- CONCL ---
    e.reset z ∈ construct (e.jumpOfPoint Rg) := by -- --- PROOF ---
  show toRealMat e.W *ᵥ z + toRealVec e.w ∈ construct (e.jumpOfPoint Rg)
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer e.W Rg
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hinter ⟨hz, hguard⟩))))
    (mem_ofPoint (toRealVec e.w)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
