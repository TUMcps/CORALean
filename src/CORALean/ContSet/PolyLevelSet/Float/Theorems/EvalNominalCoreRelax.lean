module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Relax
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Relax

@[expose] public section

/-!
# `PolyLevelSet.relax` rounds nothing

The rows with their slacks as variables read back as the exact rows relaxed by the read-back
slacks: a slack column is `diagonalBlock b_error`, which reads as `Matrix.diagonal`, so row `i`'s
column `l` is `b_errorᵢ` at `l = i` and `0` elsewhere, `Pi.single`.
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

/-- The relaxed rows, read back, take the values of the read-back rows relaxed by the read-back
slack. -/
theorem PolyLevelSet.eval_nominalCore_relax (P : PolyLevelSet 𝕋 n) (D : Interval (Vec 𝕋 P.m))
    (x : Vec ℝ (n + P.m)) :
    (P.relax D).nominalCore.eval x
      = (P.nominalCore.relax (toRealVec P.b_error) D.nominal).eval x := by -- --- PROOF ---
  have hA : toRealMat (P.relax D).A
      = (P.nominalCore.relax (toRealVec P.b_error) D.nominal).A := by
    funext i l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp only [toRealMat, PolyLevelSet.relax, Real.PolyLevelSet.relax, Fin.append_left]
    · simp only [toRealMat, PolyLevelSet.relax, Real.PolyLevelSet.relax, Fin.append_right,
        toReal_diagonalBlock, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  show (toRealMat (P.relax D).A *ᵥ Real.PolyZonotope.monomial (P.relax D).R x
      - toRealVec (P.relax D).b : Vec ℝ P.m)
    = (P.nominalCore.relax (toRealVec P.b_error) D.nominal).A *ᵥ Real.PolyZonotope.monomial
        (P.nominalCore.relax (toRealVec P.b_error) D.nominal).R x
            - (P.nominalCore.relax (toRealVec P.b_error) D.nominal).b
  rw [hA]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
