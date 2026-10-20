module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Copies
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Copies

@[expose] public section

/-!
# `PolyLevelSet.copies` rounds nothing

The copies' rows, read back, are the read-back rows copied: entries are copied, and `zero` reads
back as `0`.

## Inputs
* `P` – polynomial level set
* `a` – number of copies
* `x` – real point

## Hypotheses
* none

## Conclusion
* the copies' rows read back as the copied rows
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The copies' rows, read back, take the values of the read-back rows' copies. -/
theorem PolyLevelSet.eval_nominalCore_copies (P : PolyLevelSet 𝕋 n) (a : ℕ)
    (x : Vec ℝ (a * n)) : -- --- CONCL ---
    (P.copies a).nominalCore.eval x = (P.nominalCore.copies a).eval x := by -- --- PROOF ---
  have hA : toRealMat (P.copies a).A = (P.nominalCore.copies a).A := by
    funext x y
    simp only [toRealMat, PolyLevelSet.copies, Real.PolyLevelSet.copies, repBlockDiag]
    split_ifs
    · rfl
    · exact toReal_zero
  show toRealMat (P.copies a).A *ᵥ Real.PolyZonotope.monomial (P.copies a).R x
      - toRealVec (P.copies a).b
    = (P.nominalCore.copies a).A *ᵥ Real.PolyZonotope.monomial (P.nominalCore.copies a).R x
      - (P.nominalCore.copies a).b
  rw [hA]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
