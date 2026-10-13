import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell
import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound

/-!
# `isIntersecting_` of CORA's cell branch is unsound at `==`

For the single constraint `x = 0` (one `==` row, as a cell `{'=='}`) and the box `[0, 1]`, the
function `x` has range `[0, 1]` there, so the level set `{0}` meets the box, yet the cell branch
tests `lb < 0` at `==` with `lb = 0` and answers `false`, which `isIntersecting_` reads as
"disjoint" (read from the source, not run).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The level set `{x | x = 0}`. -/
def LevelSet.aux_L : LevelSet 1 := ⟨1, fun x => x, fun _ => .eq⟩

/-- The box `[0, 1]`. -/
def LevelSet.aux_box : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩

/-- The bounds `(0, 1)` of the function over the box. -/
def LevelSet.aux_B : Fin 1 → ℝ × ℝ := fun _ => (0, 1)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.isIntersecting_cell_counterexample :
    LevelSet.aux_L.construct ∩ LevelSet.aux_box.construct ≠ ∅ ∧
      (∀ i, IsRangeBound (fun x => LevelSet.aux_L.f x i)
        LevelSet.aux_box.construct (LevelSet.aux_B i).1 (LevelSet.aux_B i).2) ∧
      ¬ LevelSet.isIntersecting_cell 0 LevelSet.aux_L.op LevelSet.aux_B := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_⟩
  · -- the point `0` is in both
    intro h
    have : (fun _ => (0 : ℝ) : Vec ℝ 1) ∈ (∅ : Set (Vec ℝ 1)) := by
      rw [← h]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [LevelSet.aux_L, CompOp.holds]
      · exact ⟨le_rfl, zero_le_one⟩
    exact this
  · -- the range of `x` over `[0, 1]` is `[0, 1]`
    intro i x hx
    have := hx i
    exact ⟨this.1, this.2⟩
  · -- the test reads `0 < 0` at the one `==` row
    intro h
    have := h (0 : Fin 1)
    simp [LevelSet.aux_L, LevelSet.aux_B] at this


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
