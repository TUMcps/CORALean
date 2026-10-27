module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.ConZonotope.Real.Theorems.CompactExact
public import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceLiftByOuter

@[expose] public section

/-!
# `ConZonotope.reduce` over-approximates

Compacting leaves the set as it is (`compact_exact`); above the generator count, lifting, reducing
at Girard's partition and reading the rows back over-approximates (`reduceLiftBy_outer`, at any
partition); at or below it, the compacted set is returned.

## Inputs
* `cZ` – constrained zonotope
* `o` – target degree-of-freedom order

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       01-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.reduce o).construct := by -- --- PROOF ---
  rw [← ConZonotope.compact_exact cZ]
  unfold ConZonotope.reduce
  dsimp only
  split_ifs with hlt
  · exact ConZonotope.reduceLiftBy_outer cZ.compact _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
