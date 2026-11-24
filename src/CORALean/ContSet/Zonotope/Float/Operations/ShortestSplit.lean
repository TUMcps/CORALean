module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Sort

@[expose] public section

/-!
# `Zonotope.shortestSplit`

The split of CORA's `nnGeneratorReductionLayer` in `𝕋`, in CORA.cpp's order: each generator's
length `‖g‖₁` summed over the coordinates in order (rounded up), the generators ranked by it
ascending with ties in index order (a stable sort, CORA.cpp's `argsort`), the first `k` kept.

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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` shortest generators by `‖g‖₁`, against the rest. -/
def Zonotope.shortestSplit (Z : Zonotope (Vec 𝕋 n)) (k : ℕ) (hlt : k < Z.h) :
    Split (Fin Z.h) into (Fin k) ⊕ (Fin (Z.h - k)) :=
  let length : Vector 𝕋 Z.h := Vector.ofFn fun j => sumUp fun i => absolute (Z.G j i)
  (Partition.split k (Z.h - k)).reindex
    ((sortPerm fun j₁ j₂ => le length[j₁] length[j₂]).symm.trans
      (finCongr (Nat.add_sub_cancel' (le_of_lt hlt)).symm))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
