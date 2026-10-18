module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Col
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

/-!
# Regrouping a generator sum by exponent column

Split out of `Compact.lean` (issue #62): mentions no set, so
`Theorems/CompactGensExact.lean` reuses it unchanged for the constrained
constraint matrix, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `sum_monomial_merge` below needs it
theorem PolyZonotope.aux_monomial_congr {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    {i j : Fin h} (hij : PolyZonotope.col E i = PolyZonotope.col E j) :
    PolyZonotope.monomial E a i = PolyZonotope.monomial E a j := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => congrArg (fun e => a k ^ e) (congrFun hij k)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Regrouping a generator sum along any column-preserving `r`, then keeping
only the columns `s` names. Every generator-side step of `compact` is this at
some `r` and `s`, and it mentions no set, so a constraint block reuses it. -/
theorem PolyZonotope.sum_monomial_merge {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (a : Fin p → ℝ) (r : Fin h → Fin h) (s : Finset (Fin h))
    (hcol : ∀ i, PolyZonotope.col E (r i) = PolyZonotope.col E i)
    (hs : ∀ j ∉ s, PolyZonotope.fiberSum r G j = 0) : -- --- STMT ---
    (∑ i, PolyZonotope.monomial E a i • G i)
      = ∑ j ∈ s, PolyZonotope.monomial E a j • PolyZonotope.fiberSum r G j := by -- --- PROOF ---
  have hall : (∑ i, PolyZonotope.monomial E a i • G i)
      = ∑ j, PolyZonotope.monomial E a j • PolyZonotope.fiberSum r G j := by
    rw [← Finset.sum_fiberwise Finset.univ r fun i => PolyZonotope.monomial E a i • G i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PolyZonotope.fiberSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hri : r i = j := (Finset.mem_filter.mp hi).2
    have hcij : PolyZonotope.col E i = PolyZonotope.col E j := by
      rw [← hri]; exact (hcol i).symm
    rw [PolyZonotope.aux_monomial_congr E a hcij]
  rw [hall]
  refine (Finset.sum_subset (Finset.subset_univ s) fun j _ hj => ?_).symm
  rw [hs j hj, smul_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
