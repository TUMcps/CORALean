module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit

@[expose] public section

/-!
# `Zonotope.girardKeep`

Girard's ranking [1, Sec. 3.4] at a given number of kept generators: the `k` generators with the
largest metric `‖g‖₁ - ‖g‖∞` against the rest, which is what CORA's `pickedGeneratorsFast` returns
for `nUnreduced = k`. `girardSplit` is the case `k = (o - 1) n`; a caller whose order is not an
integer multiple of the dimension, as `ConZonotope.reduce`'s lifted zonotope, names the count
instead.

## Inputs
* `Z` – zonotope
* `k` – number of generators kept

## Hypotheses
* `hk` – at most the generator count

## Output
* split into kept and absorbed generators

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` generators Girard's metric ranks first, against the rest. Sorting is ascending, so the
metric enters negated. -/
noncomputable def Zonotope.girardKeep (Z : Zonotope (Vec ℝ n)) (k : ℕ) (hk : k ≤ Z.h) :
    Split (Fin Z.h) into (Fin k) ⊕ (Fin (Z.h - k)) :=
  (Partition.split k (Z.h - k)).reindex
    ((Tuple.sort fun j => -Z.girardMetric j).symm.trans
      (finCongr (Nat.add_sub_cancel' hk).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
