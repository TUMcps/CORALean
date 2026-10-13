module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.HybridDynamics.Operations.JumpFloat

@[expose] public section

/-!
# `Transition.jumpFloat` holds the reset image

`Transition.jump_outer` at a float zonotope, and the same bargain: `R` encloses
the state at the jump, `Rg` its intersection with the guard, and the reset
image lands in `jumpFloat Rg`. `Location.guardIntersectFloat` is what computes
such an `Rg`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Transition.jumpFloat_outer (e : Transition G L 𝕋 n) {R Rg : Zonotope (Vec 𝕋 n)}
    (hinter : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ n}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpFloat Rg) := by -- --- PROOF ---
  show Scalar.toRealMat e.W *ᵥ z + Scalar.toRealVec e.w ∈ construct (e.jumpFloat Rg)
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) e.W Rg
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hinter ⟨hz, hguard⟩))))
    (Interval.zonotope_contains _ (Interval.mem_point e.w)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
