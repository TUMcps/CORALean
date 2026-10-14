module

public import CORALean.Specification.STL.Operations.TreeMaximumTimeFrom

@[expose] public section

/-!
# The offset of maximumTime is added

Starting `maximumTime`'s recursion at the offset `time` adds `time` to the result: every clause is
increasing with slope one in `time`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.maximumTimeFrom_eq_add (φ : STL.Tree n) (time : ℝ≥0) :
    φ.maximumTimeFrom time = time + φ.maximumTimeFrom 0 := by -- --- PROOF ---
  induction φ generalizing time with
  | tt | ff | cmp => simp [STL.Tree.maximumTimeFrom]
  | not φ ih => exact ih time
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.maximumTimeFrom, ihφ time, ihψ time, max_add_add_left]
  | next a φ ih =>
    simp only [STL.Tree.maximumTimeFrom, ih (a + time), ih (a + 0)]
    ring
  | «finally» a b φ ih | globally a b φ ih =>
    simp only [STL.Tree.maximumTimeFrom, ih time]
    ring
  | «until» a b φ ψ ihφ ihψ | release a b φ ψ ihφ ihψ =>
    simp only [STL.Tree.maximumTimeFrom, ihφ time, ihψ time, max_add_add_left]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
