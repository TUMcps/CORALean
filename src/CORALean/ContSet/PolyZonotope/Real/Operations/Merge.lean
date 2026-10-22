module

public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import CORALean.ContSet.PolyZonotope.Real.Operations.MergeKeep
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `PolyZonotope.merge`

[1, Prop. 3.3]: equal exponent columns are one monomial, so their generators add and one column
carries them. What `compact` does, minus everything else: a generator that came out zero keeps
its column and no factor is dropped, because `sortPlus` needs the join and nothing further. [1]
merges neighbours in one pass over a *sorted* matrix (`O(p h)`); the specification here joins
every equal column at once and states no hypothesis. [1] calls the result regular; in general
it is not: equal columns are gone (`merge_col_injective`) but an all-zero one is not. Sorted it
stays sorted (`merge_sorted`).

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with equal-exponent generators merged

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The kept columns of a merge, indexed by a plain count and in order. -/
noncomputable def PolyZonotope.aux_mergeIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (j : Fin (PolyZonotope.mergeKeep E).card) : Fin h :=
  (PolyZonotope.mergeKeep E).orderIsoOfFin rfl j


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together, one column per class kept. -/
noncomputable def PolyZonotope.merge (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p
  h := (PolyZonotope.mergeKeep pZ.E).card
  q := pZ.q
  c := pZ.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep pZ.E) pZ.G
                  (PolyZonotope.aux_mergeIdx pZ.E j)
  E := fun k j => pZ.E k (PolyZonotope.aux_mergeIdx pZ.E j)
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
