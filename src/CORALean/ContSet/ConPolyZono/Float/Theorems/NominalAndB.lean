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

theorem ConPolyZono.nominal_andB (C₁ C₂ : ConPolyZono 𝕋 n) :
    (ConPolyZono.andB C₁ C₂).nominal
      = Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.andD C₁ C₂) := by
  -- the exact layer's record spelled out, so the field rewrites below have a term to match
  have hreal : Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.andD C₁ C₂)
      = (⟨Fin.append (Fin.append (toRealVec C₁.b.inf) (toRealVec C₂.b.inf))
            fun i => toReal (C₂.c i) - toReal (C₁.c i)
              + (ConPolyZono.andD C₁ C₂).inf i,
          Fin.append (Fin.append (toRealVec C₁.b.sup) (toRealVec C₂.b.sup))
            fun i => toReal (C₂.c i) - toReal (C₁.c i)
              + (ConPolyZono.andD C₁ C₂).sup i⟩ :
        Real.Interval (Vec ℝ (C₁.m + C₂.m + n))) := rfl
  have hinf : toRealVec (Fin.append (Fin.append C₁.b.inf C₂.b.inf)
        (ConPolyZono.andAgree C₁ C₂).inf)
      = Fin.append (Fin.append (toRealVec C₁.b.inf) (toRealVec C₂.b.inf))
        fun i => toReal (C₂.c i) - toReal (C₁.c i)
          + (ConPolyZono.andD C₁ C₂).inf i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.andD, toRealVec]
    ring
  -- the upper end, the same read-back with the other endpoint of each box
  have hsup : toRealVec (Fin.append (Fin.append C₁.b.sup C₂.b.sup)
        (ConPolyZono.andAgree C₁ C₂).sup)
      = Fin.append (Fin.append (toRealVec C₁.b.sup) (toRealVec C₂.b.sup))
        fun i => toReal (C₂.c i) - toReal (C₁.c i)
          + (ConPolyZono.andD C₁ C₂).sup i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.andD, toRealVec]
    ring
  rw [hreal]
  show (⟨toRealVec (Fin.append (Fin.append C₁.b.inf C₂.b.inf)
        (ConPolyZono.andAgree C₁ C₂).inf),
      toRealVec (Fin.append (Fin.append C₁.b.sup C₂.b.sup)
        (ConPolyZono.andAgree C₁ C₂).sup)⟩ :
    Real.Interval (Vec ℝ (C₁.m + C₂.m + n))) = _
  rw [hinf, hsup]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
