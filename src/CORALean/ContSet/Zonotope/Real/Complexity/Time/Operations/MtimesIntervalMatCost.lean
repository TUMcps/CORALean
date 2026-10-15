module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMatCost`

Asserted, not proved, by reading `Operations/MtimesIntervalMat.lean`:

* `Interval.center`, `(inf + sup) / 2` entrywise: `2 * m * n`;
* `Interval.radius`, `(sup - inf) / 2` entrywise: `2 * m * n`;
* `absBound`, `|c j| + ∑ l, |G l j|` for each of the `n` coordinates: `h + 1`
  absolute values and `h` additions, at most `2 * h + 1` each;
* `radiusReach`, `∑ j, radius i j * absBound j` per output row: `2 * n` each,
  so `2 * m * n`;
* the center and the `h` generators through `center *ᵥ ·`: `h + 1` products of
  `Cost.matVec m n`;
* the diagonal generator block is `m * m` writes, its zeros included. The products write their
  own results, inside `Cost.matVec`.
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
