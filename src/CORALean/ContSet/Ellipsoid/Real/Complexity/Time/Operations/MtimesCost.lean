module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Ellipsoid.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` computes `M Q` (`n` matrix-vector products at
`m × n`, one per column of `Q`), then `(M Q) Mᵀ` (`m` more, one per column of `Mᵀ`), and `M q`.

## Inputs
* `m` – rows
* `n` – columns

## Output
* cost of `n + m + 1` matrix-vector products
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Ellipsoid.mtimes` costs at `M : Mat ℝ m n`: `n + m + 1` matrix-vector products. -/
def Ellipsoid.mtimesCost (m n : ℕ) : Cost := (n + m + 1) • Cost.matVec m n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
