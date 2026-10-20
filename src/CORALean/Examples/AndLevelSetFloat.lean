import CORALean.ContSet.LevelSet.Float.Theorems.ContainsPointSound
import CORALean.ContSet.LevelSet.Real.Theorems.AndExact
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef

/-!
# Intersecting two level sets: the constraints stacked

`LevelSet.and_`. The disc `x² + y² ≤ 1` and the open half-plane `-x < 0` give a level set
with two rows, exactly their intersection (`LevelSet.and_exact`); a float sign test
(`containsPoint`) at `Dyadic 53` certifies `(1/2, 1/4)` in the stack from exact bounds on
its two row values.

## Inputs
* none

## Output
* level set of the stacked constraints
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.AndLevelSetFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _


/-- The disc `x² + y² - 1 ≤ 0`. -/
noncomputable def andDisc : Real.LevelSet 2 where
  m := 1
  f x := ![x 0 ^ 2 + x 1 ^ 2 - 1]
  op := ![.le]

/-- The open half-plane `-x < 0`. -/
noncomputable def andHalf : Real.LevelSet 2 where
  m := 1
  f x := ![-x 0]
  op := ![.lt]

/-- The two stacked: `x² + y² ≤ 1` and `x > 0`, exactly the intersection. -/
theorem stack_exact : (andDisc.and_ andHalf).construct = andDisc.construct ∩ andHalf.construct :=
  Real.LevelSet.and_exact andDisc andHalf


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stack with its functions dropped, which the sign test never calls, so it can run. -/
def stackOps : Real.LevelSet 2 :=
  Real.LevelSet.and_ ⟨1, fun _ => 0, ![.le]⟩ ⟨1, fun _ => 0, ![.lt]⟩

/-- Row values at `(1/2, 1/4)`: `-11/16` and `-1/2`, exactly. -/
def Bp : Fin 2 → Interval D := ![⟨d (-11) (-4), d (-11) (-4)⟩, ⟨d (-1) (-1), d (-1) (-1)⟩]

#eval LevelSet.containsPoint (𝕋 := D) stackOps Bp   -- true

set_option maxRecDepth 4096 in
/-- `(1/2, 1/4)` is in the stack, by the float sign test. -/
theorem stack_mem : -- --- CONCL ---
    (![1 / 2, 1 / 4] : Vec ℝ 2) ∈ (andDisc.and_ andHalf).construct := by -- --- PROOF ---
  -- the sign test is `true` by evaluation; the bounds are the exact row values
  refine LevelSet.containsPoint_sound (𝕋 := D) (andDisc.and_ andHalf) Bp _ ?_ rfl
  intro i
  fin_cases i
  · simp [Real.LevelSet.and_, andDisc, andHalf, Bp, Fin.append, Fin.addCases, toReal_d]
    norm_num
  · simp [Real.LevelSet.and_, andDisc, andHalf, Bp, Fin.append, Fin.addCases, toReal_d]

end CORALean.Examples.AndLevelSetFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
