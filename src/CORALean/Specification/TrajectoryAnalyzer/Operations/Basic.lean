module

public import CORALean.Specification.TrajectoryAnalyzer.TrajectoryAnalyzer

@[expose] public section

/-!
# `TrajectoryAnalyzer/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ===============================  `TrajectoryAnalyzer.mapTime`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The analyzer with the time points of its trajectory mapped by `f`. -/
def TrajectoryAnalyzer.mapTime {T T' 𝕋 : Type} {S : ℕ → Type} {n : ℕ} (f : T → T')
    (obj : TrajectoryAnalyzer T 𝕋 S n) : TrajectoryAnalyzer T' 𝕋 S n :=
  ⟨obj.aps, ⟨obj.traj.t.map f, obj.traj.x, obj.traj.loc⟩⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
