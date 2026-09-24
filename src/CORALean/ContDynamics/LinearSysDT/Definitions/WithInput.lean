import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# A system paired with its input set

`Reach.Params` is one plain `Type`, not indexed by `n`, so it cannot hold a
per-dimension representation — the input set `U` a step's `Trajectory` reads
from. Bundled with the system itself instead: `Reach LinearSysDT.WithInput`
is then read off the system it is asked about, exactly as `sys.A` is.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinearSysDT` paired with the input set every step draws from. -/
structure LinearSysDT.WithInput (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinearSysDT 𝕋 n
  U : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
