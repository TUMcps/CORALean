module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Switch
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Switch
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `PolyLevelSet.switch` rounds nothing

The switched rows, read back, are the read-back rows switched: halving and negating are exact.

## Inputs
* `P` – polynomial level set
* `e` – exponent of the switching monomial
* `s` – sign of each row
* `x` – real point

## Hypotheses
* none

## Conclusion
* the switched rows read back as the exact switch
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The switched rows, read back, take the values of the read-back rows switched. -/
theorem PolyLevelSet.eval_nominalCore_switch (P : PolyLevelSet 𝕋 n) (e : Fin n → ℕ)
    (s : Fin P.m → Bool) (x : Vec ℝ n) : -- --- CONCL ---
    (P.switch e s).nominalCore.eval x = (P.nominalCore.switch e s).eval x := by -- --- PROOF ---
  have hA : toRealMat (P.switch e s).A = (P.nominalCore.switch e s).A := by
    funext i l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp only [toRealMat, PolyLevelSet.switch, Real.PolyLevelSet.switch, Fin.append_left]
    · simp only [toRealMat, PolyLevelSet.switch, Real.PolyLevelSet.switch, Fin.append_right]
      cases s i <;> simp only [Bool.false_eq_true, if_false, if_true, toReal_neg, toReal_half,
        toRealVec] <;> ring
  have hb : toRealVec (P.switch e s).b = (P.nominalCore.switch e s).b := by
    funext i
    simp only [toRealVec, PolyLevelSet.switch, Real.PolyLevelSet.switch, toReal_half]
    ring
  show toRealMat (P.switch e s).A *ᵥ Real.PolyZonotope.monomial (P.switch e s).R x
      - toRealVec (P.switch e s).b
    = (P.nominalCore.switch e s).A *ᵥ Real.PolyZonotope.monomial (P.nominalCore.switch e s).R x
      - (P.nominalCore.switch e s).b
  rw [hA, hb]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
