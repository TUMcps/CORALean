module

public import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
public import CORALean.ContSet.ConZonotope.Float.Theorems.CompactExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftByOuter

@[expose] public section

/-!
# `ConZonotope.reduce` over-approximates, in floats

Compacting leaves the set as it is (`compact_exact`); above the generator count, lifting, reducing
at Girard's partition and reading the rows back over-approximates (`reduceLiftBy_outer`, at any
partition, the box rounded up); at or below it, the compacted set is returned.

## Inputs
* `cZ` – float constrained zonotope
* `o` – target degree-of-freedom order

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (o : ℕ) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.reduce o).construct := by -- --- PROOF ---
  rw [← ConZonotope.compact_exact cZ]
  unfold ConZonotope.reduce
  dsimp only
  split_ifs with hlt
  · exact ConZonotope.reduceLiftBy_outer cZ.compact _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
