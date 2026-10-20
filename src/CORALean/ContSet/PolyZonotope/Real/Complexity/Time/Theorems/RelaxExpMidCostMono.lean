module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.RelaxDriftCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpMidCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMidCost_mono`

Monotone in the factor count.

## Inputs
* `p` – number of factors
* `p'` – larger factor count
* `d` – kept dependent generators
* `d'` – larger kept dependent count
* `q` – independent generator count
* `q'` – larger independent count
* `n` – dimension

## Hypotheses
* `h` – factor count grows
* `hd` – kept dependent count grows
* `hq` – independent count grows

## Conclusion
* the cost does not decrease
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor and independent counts, and in the kept dependent count. -/
theorem PolyZonotope.relaxExpMidCost_mono {p p' d d' q q' : ℕ} (n : ℕ) (h : p ≤ p')
    (hd : d ≤ d') (hq : q ≤ q') :
    PolyZonotope.relaxExpMidCost n p d q ≤ PolyZonotope.relaxExpMidCost n p' d' q' := by
  have := PolyZonotope.relaxDriftCost_mono h
  simp only [PolyZonotope.relaxExpMidCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  have g : n * (d + q + 3) + p * (d + 1) ≤ n * (d' + q' + 3) + p' * (d' + 1) := by gcongr
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
