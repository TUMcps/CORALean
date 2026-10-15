module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import CORALean.ContDynamics.NeurNetContrSys.Operations.AugmentFloat

@[expose] public section

/-!
# `augmentFloat` reads as `augment`

Entry by entry: the plant's own entries read as themselves, and the zeros as `0` by
`toReal_zero`. So the float reachability of the augmented system in `𝕋` reaches the real
augmented system, which `augment_flow` ties to the closed loop.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.toRealMat_augmentFloat (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) :
    Scalar.toRealMat sys.augmentFloat.A = sys.augment.A ∧
      Scalar.toRealVec sys.augmentFloat.c = sys.augment.c := by -- --- PROOF ---
  constructor
  · funext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [NeurNetContrSys.augmentFloat, NeurNetContrSys.augment, Scalar.toRealMat_apply] <;>
      exact toReal_zero
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [NeurNetContrSys.augmentFloat, NeurNetContrSys.augment, Scalar.toRealVec_apply]
    · simp only [NeurNetContrSys.augmentFloat, NeurNetContrSys.augment, Scalar.toRealVec_apply,
        Fin.append_right]
      exact toReal_zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
