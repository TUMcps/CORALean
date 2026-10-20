import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.LevelSet.Float.Theorems.IsIntersectingCellOuter
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef

/-!
# A level set certified disjoint from a box, at float bounds

The unit disc `x² + y² - 1 ≤ 0` and the box `[2, 3]²`. The row ranges over the box in `[7, 17]`,
which stays above `0`, so `isIntersecting_cell` at `Dyadic 53` answers `false` and the disc has
no point in the box — the nearest corner `(2, 2)` is at distance `√8` from the origin, well
outside the unit disc.

`LevelSet.isIntersecting_cell_outer` is applied to these very bounds; a `true` decides nothing.

## Inputs
* none

## Output
* box from two to three in both coordinates
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.LevelSetCellFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `[2, 3]²`. -/
def box : Interval (Vec D 2) := ⟨fun _ => d 2 0, fun _ => d 3 0⟩

/-- The disc alone. -/
noncomputable def levelDisc : CORALean.Real.LevelSet 2 where
  m := 1
  f x := ![x 0 ^ 2 + x 1 ^ 2 - 1]
  op := ![.le]

/-- Range of `x² + y² - 1` over the box: `[7, 17]`. -/
def Bbox : Fin 1 → Interval D := ![⟨d 7 0, d 17 0⟩]

#eval LevelSet.isIntersecting_cell (m := 1) (d 0 0 : D) ![.le] Bbox  -- false

set_option maxRecDepth 4096 in
/-- No point of the disc lies in the box. -/
theorem disc_box_disjoint : -- --- CONCL ---
    levelDisc.construct ∩ box.construct = ∅ := by -- --- PROOF ---
  -- the test returns `false`; no `=` row, tolerance `0`, and `[7, 17]` bounds the row over the box
  refine LevelSet.isIntersecting_cell_outer (𝕋 := D) levelDisc (fun i => ?_) box Bbox
    (tol := d 0 0) ?_ ?_ rfl
  · fin_cases i; simp [levelDisc]
  · simp [toReal_d]
  · -- the bounds enclose the row over the box
    intro i x hx
    rcases i with ⟨_ | _, hi⟩
    swap; · simp [levelDisc] at hi
    have h0 : toReal (d 2 0) ≤ x 0 ∧ x 0 ≤ toReal (d 3 0) := hx 0
    have h1 : toReal (d 2 0) ≤ x 1 ∧ x 1 ≤ toReal (d 3 0) := hx 1
    simp only [toReal_d] at h0 h1
    simp only [Bbox, levelDisc, Fin.zero_eta, Matrix.cons_val_zero, toReal_d]
    norm_num at h0 h1 ⊢
    constructor <;> nlinarith

end CORALean.Examples.LevelSetCellFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
