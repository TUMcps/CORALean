module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.Col
public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# A column that is not its class's representative gathers nothing

## Inputs
* `E` – exponent matrix
* `Gr` – real generator row
* `j` – column index

## Hypotheses
* `hj` – column is not a kept one

## Conclusion
* the exact fibre sum at that column is zero
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The least index of a class is the least index of its own class, which makes
a non-representative's fibre empty. The two finsets are named rather than left
to unification, `rep` unfolding to a `min'` over a filter. -/
theorem PolyZonotope.aux_rep_idem (E : Fin p → Fin h → ℕ) (i : Fin h) : -- --- CONCL ---
    Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i)
      = Real.PolyZonotope.rep E i := by -- --- PROOF ---
  have hcol : Real.PolyZonotope.col E (Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i))
      = Real.PolyZonotope.col E i := by
    rw [Real.PolyZonotope.col_rep, Real.PolyZonotope.col_rep]
  have h₁ : Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i)
      ≤ Real.PolyZonotope.rep E i :=
    Finset.min'_le
      (Finset.univ.filter fun i' => Real.PolyZonotope.col E i'
        = Real.PolyZonotope.col E (Real.PolyZonotope.rep E i))
      (Real.PolyZonotope.rep E i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have h₂ : Real.PolyZonotope.rep E i
      ≤ Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i) :=
    Finset.min'_le
      (Finset.univ.filter fun i' => Real.PolyZonotope.col E i' = Real.PolyZonotope.col E i)
      (Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol⟩)
  exact le_antisymm h₁ h₂


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.fiber_eq_zero_of_notMem (E : Fin p → Fin h → ℕ) (Gr : Fin h → ℝ)
    {j : Fin h} (hj : j ∉ PolyZonotope.repKeep E) : -- --- CONCL ---
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E) Gr j = 0 := by -- --- PROOF ---
  rw [Real.PolyZonotope.fiberSum]
  refine Finset.sum_eq_zero fun l hl => ?_
  exfalso
  have hrl : Real.PolyZonotope.rep E l = j := (Finset.mem_filter.mp hl).2
  refine hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  rw [← hrl, PolyZonotope.aux_rep_idem]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
