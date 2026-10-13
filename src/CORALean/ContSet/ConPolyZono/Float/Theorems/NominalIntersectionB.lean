module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionB
public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionB
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionD
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecAppend

@[expose] public section

/-!
# The bound `intersectionB` reads back to the exact layer's, at the tolerance `intersectionD`

The two systems' own bounds read back by `toRealVec_append`, twice over, and
the agreement rows' bound is `intersectionD` by construction.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominal_intersectionB (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (ConPolyZono.intersectionB cPZ₁ cPZ₂).nominal
      = Real.ConPolyZono.intersectionB (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.intersectionD cPZ₁ cPZ₂) := by -- --- PROOF ---
  -- the exact layer's record spelled out, so the field rewrites below have a term to match
  have hreal : Real.ConPolyZono.intersectionB (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.intersectionD cPZ₁ cPZ₂)
      = (⟨Fin.append (Fin.append (toRealVec cPZ₁.b.inf) (toRealVec cPZ₂.b.inf))
            fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
              + (ConPolyZono.intersectionD cPZ₁ cPZ₂).inf i,
          Fin.append (Fin.append (toRealVec cPZ₁.b.sup) (toRealVec cPZ₂.b.sup))
            fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
              + (ConPolyZono.intersectionD cPZ₁ cPZ₂).sup i⟩ :
        Real.Interval (Vec ℝ (cPZ₁.m + cPZ₂.m + n))) := rfl
  have hinf : toRealVec (Fin.append (Fin.append cPZ₁.b.inf cPZ₂.b.inf)
        (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf)
      = Fin.append (Fin.append (toRealVec cPZ₁.b.inf) (toRealVec cPZ₂.b.inf))
        fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
          + (ConPolyZono.intersectionD cPZ₁ cPZ₂).inf i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.intersectionD, toRealVec]
    ring
  -- the upper end, the same read-back with the other endpoint of each box
  have hsup : toRealVec (Fin.append (Fin.append cPZ₁.b.sup cPZ₂.b.sup)
        (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup)
      = Fin.append (Fin.append (toRealVec cPZ₁.b.sup) (toRealVec cPZ₂.b.sup))
        fun i => toReal (cPZ₂.c i) - toReal (cPZ₁.c i)
          + (ConPolyZono.intersectionD cPZ₁ cPZ₂).sup i := by
    rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]
    refine congrArg _ (funext fun i => ?_)
    simp only [ConPolyZono.intersectionD, toRealVec]
    ring
  rw [hreal]
  show (⟨toRealVec (Fin.append (Fin.append cPZ₁.b.inf cPZ₂.b.inf)
        (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf),
      toRealVec (Fin.append (Fin.append cPZ₁.b.sup cPZ₂.b.sup)
        (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup)⟩ :
    Real.Interval (Vec ℝ (cPZ₁.m + cPZ₂.m + n))) = _
  rw [hinf, hsup]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
