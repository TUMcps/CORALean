import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.LevelSet.Float.Theorems.ContainsPointSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef

/-!
# A point certified in a level set, at float bounds

The unit disc `x² + y² - 1 ≤ 0` cut by the open half-plane `-x < 0` and the line `x - 2y = 0`,
a `LevelSet` with three rows (`≤`, `<`, `=`). A level set keeps its real function, which
nothing evaluates, so what runs at `Dyadic 53` is the sign test on stored bounds of that
function: `containsPoint` certifies the point `(1/2, 1/4)` from exact bounds on the three row
values, and refuses a point outside the disc, `(2, 0)`.

`LevelSet.containsPoint_sound` is applied to these very bounds; a `false` decides nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.LevelSetContainsFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The operators; the sign tests read nothing else of the level set. -/
def ops : Fin 3 → CORALean.Real.CompOp := ![.le, .lt, .eq]

/-- Disc, open half-plane, line. -/
noncomputable def levelSet : CORALean.Real.LevelSet 2 where
  m := 3
  f x := ![x 0 ^ 2 + x 1 ^ 2 - 1, -x 0, x 0 - 2 * x 1]
  op := ops

/-- The point `(1/2, 1/4)`. -/
noncomputable def levelPoint : Vec ℝ 2 := ![1 / 2, 1 / 4]

/-- Exact bounds on the three row values at `p`: `-11/16`, `-1/2`, `0`. -/
def B : Fin 3 → Interval D := ![⟨d (-11) (-4), d (-11) (-4)⟩, ⟨d (-1) (-1), d (-1) (-1)⟩,
  ⟨d 0 0, d 0 0⟩]

/-- `levelSet` with its function dropped, which the tests never call, so `#eval` can run them. -/
def levelOps : CORALean.Real.LevelSet 2 := ⟨3, fun _ => 0, ops⟩

#eval LevelSet.containsPoint (𝕋 := D) levelOps B  -- true

/-- Bounds at `(2, 0)`, outside the disc: `3 ≤ 0` is not certified. -/
def Bout : Fin 3 → Interval D := ![⟨d 3 0, d 3 0⟩, ⟨d (-2) 0, d (-2) 0⟩, ⟨d 2 0, d 2 0⟩]

#eval LevelSet.containsPoint (𝕋 := D) levelOps Bout  -- false

set_option maxRecDepth 4096 in
/-- The point is in the set: the three certified comparisons, read as reals. -/
theorem levelPoint_mem : levelPoint ∈ levelSet.construct := by
  refine LevelSet.containsPoint_sound (𝕋 := D) levelSet B levelPoint ?_ rfl
  intro i
  fin_cases i <;> simp [levelSet, B, levelPoint, toReal_d] <;> norm_num

end CORALean.Examples.LevelSetContainsFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
