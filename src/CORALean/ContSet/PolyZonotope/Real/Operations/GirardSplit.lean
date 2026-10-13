module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GirardMetric
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# The generators a metric ranks first, against the rest

Split out of `Reduce.lean` (issue #62), no longer `aux_`: `reduceGirard` and
`reduceGirardDependent` each need it from their own file, so neither can keep
it file-local.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; sorting is
ascending, so the metric enters negated and the dearest to box rank first. -/
noncomputable def PolyZonotope.girardSplit {m : ℕ} (metric : Fin m → ℝ) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) ⊕ (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((Tuple.sort fun l => -metric l).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
