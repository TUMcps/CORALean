module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.And
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `PolyLevelSet.and_` rounds nothing

The stored stack reads back as the exact stack of the two read-back systems: the off-blocks are
`zero`, which reads as `0`, and every other entry is copied.

## Inputs
* `P₁` – first level set
* `P₂` – second level set
* `x` – real point

## Hypotheses
* none

## Conclusion
* the stacked rows read back as the exact stack
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacked rows, read back, take the values of the stack of the read-back rows. -/
theorem PolyLevelSet.eval_nominalCore_and_ (P₁ P₂ : PolyLevelSet 𝕋 n)
    (x : Vec ℝ n) : -- --- CONCL ---
    (P₁.and_ P₂).nominalCore.eval x
      = (P₁.nominalCore.and_ P₂.nominalCore).eval x := by -- --- PROOF ---
  have hA : toRealMat (P₁.and_ P₂).A = (P₁.nominalCore.and_ P₂.nominalCore).A := by
    funext i l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
      simp [toRealMat, PolyLevelSet.and_, Real.PolyLevelSet.and_, toReal_zero]
  have hb : toRealVec (P₁.and_ P₂).b = (P₁.nominalCore.and_ P₂.nominalCore).b :=
    toRealVec_append _ _
  show toRealMat (P₁.and_ P₂).A *ᵥ _ - toRealVec (P₁.and_ P₂).b
    = (P₁.nominalCore.and_ P₂.nominalCore).A *ᵥ _ - (P₁.nominalCore.and_ P₂.nominalCore).b
  rw [hA, hb]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
