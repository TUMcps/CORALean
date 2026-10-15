module

public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.inputSet`

The input set of a location's canonical form, CORA's `canonicalForm` [1] at the location's
dynamics and sets: `B U ⊕ c ⊕ E W`, the combined input `B u + c + E w` of every stay, in the
state space. `canonicalForm` keeps the centers apart (`u_ = B c_U + c + E c_W`, `U_ = B(U - c_U) ⊕
E(W - c_W)`); their sum is this set. The reachability steps of a location read their input
here, as CORA's `linearSys/reach` runs on the canonical form. Soundness is `inputSet_outer`.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B U ⊕ c ⊕ E W`, the input set of the canonical form, in the state space. -/
def Location.inputSet (ℓ : Location S G L 𝕋 n) : S n :=
  Plus.plus (Plus.plus (Mtimes.mtimes (𝕄 := Mat ℝ) (toRealMat ℓ.dynamics.B) ℓ.U)
    (OfPoint.ofPoint (toRealVec ℓ.dynamics.c)))
    (Mtimes.mtimes (𝕄 := Mat ℝ) (toRealMat ℓ.dynamics.E) ℓ.W)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
