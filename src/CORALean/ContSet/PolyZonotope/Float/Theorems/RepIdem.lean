module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Col
public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# A class's representative is its own representative

Makes a non-representative's fibre empty: `rep` unfolds to a `min'` over a
filter, and the least index of a class is the least index of its own class.

## Inputs
* `E` – exponent matrix
* `i` – column index

## Hypotheses
* none

## Conclusion
* the representative of a representative is itself
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The least index of a class is the least index of its own class, which makes
a non-representative's fibre empty. The two finsets are named rather than left
to unification, `rep` unfolding to a `min'` over a filter. -/
theorem PolyZonotope.rep_idem (E : Fin p → Fin h → ℕ) (i : Fin h) : -- --- CONCL ---
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
