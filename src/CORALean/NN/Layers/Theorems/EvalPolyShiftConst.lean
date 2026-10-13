module

public import CORALean.NN.Layers.Operations.ShiftConst
public import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A stored shift moves the polynomial by what it landed

Read as reals it is the exact recentring, at whatever the rounded sum actually moved the
constant coefficient by.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_shiftConst (c : Fin (m + 1) → 𝕋) (s : 𝕋) (t : ℝ) :
    Real.evalPoly (fun k => toReal (shiftConst c s k)) t
      = Real.evalPoly (fun k => toReal (c k)) t
        + (toReal (addUp (c 0) s) - toReal (c 0)) := by -- --- PROOF ---
  have hco : (fun k => toReal (shiftConst c s k))
      = Real.shiftConst (fun k => toReal (c k))
        (toReal (addUp (c 0) s) - toReal (c 0)) := by
    funext k
    -- only the constant slot moves, and there the rounded sum is what landed
    by_cases hk : k = 0
    · subst hk
      show toReal (if (0 : Fin (m + 1)) = 0 then addUp (c 0) s else c 0)
        = toReal (c 0) + (if (0 : Fin (m + 1)) = 0 then
            toReal (addUp (c 0) s) - toReal (c 0) else 0)
      rw [if_pos rfl, if_pos rfl]
      ring
    · show toReal (if k = 0 then addUp (c k) s else c k)
        = toReal (c k) + (if k = 0 then toReal (addUp (c 0) s) - toReal (c 0) else 0)
      rw [if_neg hk, if_neg hk, add_zero]
  rw [hco, Real.evalPoly_shiftConst]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
