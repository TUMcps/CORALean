import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.LevelSet.Float.Theorems.ContainsPointSound
import CORALean.ContSet.LevelSet.Float.Theorems.IsIntersectingCellOuter
import CORALean.ContSet.LevelSet.Float.Theorems.RepresentsaEmptySetSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A level set, tested at float bounds

The unit disc `x² + y² - 1 ≤ 0` cut by the open half-plane `-x < 0` and the line `x - 2y = 0`,
a `LevelSet` with three rows (`≤`, `<`, `=`). A level set keeps its real function, which nothing
evaluates, so what runs at `Dyadic 53` are the sign tests on stored bounds of that function:
`containsPoint` certifies the point `(1/2, 1/4)` from exact bounds on the three row values, and
refuses a point outside the disc; `representsa_emptySet` refutes the single row `1 + sin² x ≤ 0`
from its range `[1, 2]`; `isIntersecting_cell` refutes any common point of the disc with the box
`[2, 3]²` from the row's range `[7, 17]` over the box.

Each certain answer is a guarantee, and the theorem instances below apply
`LevelSet.containsPoint_sound`, `LevelSet.representsa_emptySet_sound` and
`LevelSet.isIntersecting_cell_outer` to these very bounds; a `false` from `containsPoint` and
`representsa_emptySet`, and a `true` from `isIntersecting_cell`, decide nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.LevelSetFloat

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


/-! ## Emptiness: a row bounded away from the comparison -/

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


/-! ## Disjointness from a box -/

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
theorem disc_box_disjoint : levelDisc.construct ∩ box.construct = ∅ := by -- --- PROOF ---
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

end CORALean.Examples.LevelSetFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
