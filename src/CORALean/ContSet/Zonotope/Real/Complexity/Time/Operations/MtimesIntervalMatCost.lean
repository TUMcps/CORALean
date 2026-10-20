module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMatCost`

Asserted, not proved, by reading `Operations/MtimesIntervalMat.lean`: `Interval.center` and
`Interval.radius`, `2 * m * n` each; `absBound` for each of the `n` coordinates, at most
`2 * h + 1`; `radiusReach` per output row, `2 * n` each, so `2 * m * n`; the center and the `h`
generators through `center *ᵥ ·`, `h + 1` products of `Cost.matVec m n` (which write their own
results); and the diagonal generator block, `m * m` writes, its zeros included.

## Inputs
* `m` – matrix row count
* `n` – matrix column count
* `h` – generator count

## Output
* cost of the radius, the products and the diagonal block writes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimesIntervalMat` costs at `IM : Interval (Mat ℝ m n)` and `h` generators:
the radius, the `h + 1` products, and `m * m` writes for the diagonal block of new generators. -/
def Zonotope.mtimesIntervalMatCost (m n h : ℕ) : Cost :=
  ⟨6 * (m * n) + n * (2 * h + 1) + m * m⟩ + (h + 1) • Cost.matVec m n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
