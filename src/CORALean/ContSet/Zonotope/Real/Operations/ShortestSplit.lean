module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.shortestSplit`

The split of CORA's `nnGeneratorReductionLayer`: the generators ranked by ascending length
`‖g‖₁`, the first `k` kept and the rest passed on to be boxed. CORA keeps the shortest ones,
unlike Girard's rule, which keeps those dearest to box.

## Inputs
* `Z` – zonotope
* `k` – number of generators kept

## Hypotheses
* `hlt` – reduction needed

## Output
* split into kept and absorbed generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` shortest generators by `‖g‖₁`, against the rest. -/
noncomputable def Zonotope.shortestSplit (Z : Zonotope (Vec ℝ n)) (k : ℕ) (hlt : k < Z.h) :
    Split (Fin Z.h) into (Fin k) ⊕ (Fin (Z.h - k)) :=
  (Partition.split k (Z.h - k)).reindex
    ((Tuple.sort fun j => ∑ i, |Z.G j i|).symm.trans
      (finCongr (Nat.add_sub_cancel' (le_of_lt hlt)).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
