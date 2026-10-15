module

public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy

@[expose] public section

/-!
# `PolyZonotope.reduceByCost_mono`

Monotone in the kept and the absorbed counts, so a bound on how many generators a split keeps
and throws away gives a bound on the cost.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the kept and the absorbed counts, so a bound on how many generators a split keeps
and throws away gives a bound on the cost. -/
theorem PolyZonotope.reduceByCost_mono {p p' d d' dI dI' r r' rI rI' : ℕ} (n : ℕ) (hp : p ≤ p')
    (hd : d ≤ d') (hdI : dI ≤ dI') (hr : r ≤ r') (hI : rI ≤ rI') :
    PolyZonotope.reduceByCost n p d dI r rI ≤ PolyZonotope.reduceByCost n p' d' dI' r' rI' := by
  cost_mono [PolyZonotope.reduceByCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
