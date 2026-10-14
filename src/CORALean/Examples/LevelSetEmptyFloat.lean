import CORALean.ContSet.LevelSet.Float.Theorems.RepresentsaEmptySetSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A level set certified empty, at float bounds

The single row `1 + sin² x ≤ 0` has the range `[1, 2]`, bounded away from the comparison, so no
point satisfies it. The function itself is not evaluated: `representsa_emptySet` at `Dyadic 53`
reads the stored bounds `[1, 2]` of the row and the operator, and refutes the row.

`LevelSet.representsa_emptySet_sound` is applied to these very bounds; a `false` decides
nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.LevelSetEmptyFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `1 + sin² x ≤ 0` has range `[1, 2]`, so it is empty. -/
noncomputable def levelEmpty : CORALean.Real.LevelSet 1 where
  m := 1
  f x := ![1 + Real.sin (x 0) ^ 2]
  op := ![.le]

/-- `levelEmpty` with its function dropped. -/
def levelEmptyOps : CORALean.Real.LevelSet 1 := ⟨1, fun _ => 0, ![.le]⟩

def O : Fin 1 → Interval D := ![⟨d 1 0, d 2 0⟩]

#eval LevelSet.representsa_emptySet (𝕋 := D) levelEmptyOps O  -- true

set_option maxRecDepth 4096 in
/-- The test refutes the one row, so the level set is empty. -/
theorem levelEmpty_eq : levelEmpty.construct = ∅ := by -- --- PROOF ---
  -- the sign test is `true` by evaluation; the bounds `[1, 2]` enclose `1 + sin² x`
  refine LevelSet.representsa_emptySet_sound (𝕋 := D) levelEmpty O ?_ (by norm_num [levelEmpty]) rfl
  intro i x
  rcases i with ⟨_ | _, hi⟩
  swap; · simp [levelEmpty] at hi
  simp only [levelEmpty, O, Fin.zero_eta, Matrix.cons_val_zero, toReal_d]
  constructor <;> norm_num <;> nlinarith [Real.sin_sq_le_one (x 0), sq_nonneg (Real.sin (x 0))]

end CORALean.Examples.LevelSetEmptyFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
