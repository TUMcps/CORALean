module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GirardMetric
public import CORALean.Global.Partition
public import CORALean.Global.Sort

@[expose] public section

/-!
# The generators a metric ranks first, against the rest, over a floating-point scalar

Split out of `Reduce.lean` (issue #62), no longer `aux_`: `reduceGirard` and
`reduceGirardDependent` each need it from their own file, so neither can keep
it file-local.

## Inputs
* `𝕋` – float scalar type
* `m` – number of generators
* `metric` – score per generator
* `k` – number of generators kept

## Output
* split of the generators into the top scored and the rest
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; the
comparator ranks the larger metric first, CORA's descending sort. -/
def PolyZonotope.girardSplit {𝕋 : Type} [FloatOps 𝕋] {m : ℕ} (metric : Fin m → 𝕋) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) ⊕ (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
