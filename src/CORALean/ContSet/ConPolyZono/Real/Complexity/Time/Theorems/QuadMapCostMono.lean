module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.QuadMapCost

@[expose] public section

/-!
# `ConPolyZono.quadMapCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.

## Inputs
* `h` – smaller dependent generators
* `h'` – larger dependent generators
* `qI` – smaller independent generators
* `q'` – larger independent generators
* `m` – number of matrices
* `n` – ambient dimension
* `p` – number of factors
* `mC` – number of constraints
* `q` – constraint generators

## Hypotheses
* `hh` – dependent generator counts are ordered
* `hq` – independent generator counts are ordered

## Conclusion
* the cost is monotone in both generator counts
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.quadMapCost_mono {h h' qI q' : ℕ} (m n p mC q : ℕ) (hh : h ≤ h')
    (hq : qI ≤ q') : -- --- CONCL ---
    ConPolyZono.quadMapCost m n p h qI mC q ≤
      ConPolyZono.quadMapCost m n p h' q' mC q := by -- --- PROOF ---
  -- `dependent` writes the result; the comparison is the map's at the counts it leaves
  have a := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simp only [ConPolyZono.quadMapCost, ConPolyZono.dependentCost, PolyZonotope.dependentCost,
    Cost.le_iff, Cost.ops_add] at a ⊢
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
