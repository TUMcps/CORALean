import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# A system paired with its input set

`Reach.Params` is one plain `Type`, not indexed by `n`, so it cannot hold a
per-dimension representation — the input set `U` a step's `Trajectory` reads
from. Bundled with the system itself instead, exactly as `LinearSysDT
.WithInput` is.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinParamSysDT` paired with the input set every step draws from. -/
structure LinParamSysDT.WithInput (𝕄 : ℕ → ℕ → Type) [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
    (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinParamSysDT 𝕄 n
  U : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
