import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Operations.AndB
import CORALean.ContSet.ConPolyZono.Real.Operations.AndB
import CORALean.ContSet.ConPolyZono.Float.Operations.AndAgree
import CORALean.ContSet.ConPolyZono.Float.Theorems.AndD
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecAppend

/-!
# The bound `andB` reads back to the exact layer's, at the tolerance `andD`

The two systems' own bounds read back by `toRealVec_append`, twice over, and
the agreement rows' bound is `andD` by construction.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominal_andB (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) :
    (ConPolyZono.andB cPZ₁ cPZ₂).nominal
      = Real.ConPolyZono.andB (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.andD cPZ₁ cPZ₂) := by -- --- PROOF ---
  -- the exact layer's record spelled out, so the field rewrites below have a term to match
  have hreal : Real.ConPolyZono.andB (nominal cPZ₁) (nominal cPZ₂) (ConPolyZono.andD cPZ₁ cPZ₂)
      = (⟨Fin.append (Fin.append (toRealVec cPZ₁.b.inf) (toRealVec cPZ₂.b.inf))
            fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
              + (ConPolyZono.andD cPZ₁ cPZ₂).inf i,
          Fin.append (Fin.append (toRealVec cPZ₁.b.sup) (toRealVec cPZ₂.b.sup))
            fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
              + (ConPolyZono.andD cPZ₁ cPZ₂).sup i⟩ :
        Real.Interval (Vec ℝ (cPZ₁.m + cPZ₂.m + n))) := rfl
  have hinf : toRealVec (Fin.append (Fin.append cPZ₁.b.inf cPZ₂.b.inf)
        (ConPolyZono.andAgree cPZ₁ cPZ₂).inf)
      = Fin.append (Fin.append (toRealVec cPZ₁.b.inf) (toRealVec cPZ₂.b.inf))
        fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
          + (ConPolyZono.andD cPZ₁ cPZ₂).inf i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.andD, toRealVec]
    ring
  -- the upper end, the same read-back with the other endpoint of each box
  have hsup : toRealVec (Fin.append (Fin.append cPZ₁.b.sup cPZ₂.b.sup)
        (ConPolyZono.andAgree cPZ₁ cPZ₂).sup)
      = Fin.append (Fin.append (toRealVec cPZ₁.b.sup) (toRealVec cPZ₂.b.sup))
        fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
          + (ConPolyZono.andD cPZ₁ cPZ₂).sup i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.andD, toRealVec]
    ring
  rw [hreal]
  show (⟨toRealVec (Fin.append (Fin.append cPZ₁.b.inf cPZ₂.b.inf)
        (ConPolyZono.andAgree cPZ₁ cPZ₂).inf),
      toRealVec (Fin.append (Fin.append cPZ₁.b.sup cPZ₂.b.sup)
        (ConPolyZono.andAgree cPZ₁ cPZ₂).sup)⟩ :
    Real.Interval (Vec ℝ (cPZ₁.m + cPZ₂.m + n))) = _
  rw [hinf, hsup]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
