import CORALean.ContSet.Capsule.Real.Instances
import CORALean.ContSet.ContSet.Definitions.IsFullDim

/-!
# CORA's `capsule/isFullDim` is wrong for a thin capsule

CORA's `@capsule/isFullDim.m` returns `~isempty(C.r) && C.r > 0`. The segment of radius `0` and
generator `1` in `ℝ¹` is the interval `[-1, 1]`, which is full-dimensional there, but the radius is
not positive. `Capsule.isFullDim_iff` gives the exact characterisation; this is the witness that
CORA's formula differs from it.

Not collected in `Theorems/API.lean`: it needs the `ContSet` instance, which that API feeds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA answers `C.r > 0`; the segment `[-1, 1]` in `ℝ¹` (`r = 0`, `g = 1`) is full-dimensional
although `r = 0`. -/
theorem Capsule.isFullDim_cora_counterexample :
    ∃ C : Capsule 1, ContSet.IsFullDim C ∧ ¬ 0 < C.r :=
  ⟨⟨0, fun _ => 1, 0⟩,
    (Capsule.isFullDim_iff _).mpr (Or.inr ⟨le_rfl, Or.inr ⟨rfl, fun h => by
      have := congrFun h 0; simp at this⟩⟩),
    lt_irrefl _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
