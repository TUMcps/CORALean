module

public import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit

@[expose] public section

/-!
# `Zonotope.girardKeep` over a floating-point scalar

Girard's ranking at a given number of kept generators, as over ℝ: the `k` generators with the
largest metric `‖g‖₁ - ‖g‖∞`, computed in `𝕋` and sorted by `sortPerm` as in `girardSplit`, against
the rest. CORA's `pickedGeneratorsFast` for `nUnreduced = k`. A misranking costs precision alone,
`reduceBy_outer` holding at every partition.

## Inputs
* `Z` – zonotope
* `k` – number of generators kept

## Hypotheses
* `hk` – at most the generator count

## Output
* split into kept and absorbed generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` generators Girard's metric ranks first, against the rest; the comparator ranks the
larger metric first, CORA's descending sort. -/
def Zonotope.girardKeep (Z : Zonotope (Vec 𝕋 n)) (k : ℕ) (hk : k ≤ Z.h) :
    Split (Fin Z.h) into (Fin k) ⊕ (Fin (Z.h - k)) :=
  let metric : Vector 𝕋 Z.h := Vector.ofFn Z.girardMetric        -- ‖g‖₁ - ‖g‖∞ per generator
  (Partition.split k (Z.h - k)).reindex
    ((sortPerm fun j₁ j₂ => le metric[j₂] metric[j₁]).symm.trans
      (finCongr (Nat.add_sub_cancel' hk).symm))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
