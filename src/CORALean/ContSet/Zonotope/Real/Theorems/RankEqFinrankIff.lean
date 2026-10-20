module

public import CORALean.ContSet.Zonotope.Real.Operations.Rank
public import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff

@[expose] public section

/-!
# A zonotope is full-dimensional iff its generators have full rank

`rank = dim` is how CORA's `isFullDim` tests it (`dim(Z) == rank(Z.G)`). The generators span the
ambient space exactly when the span has the ambient dimension, so this is
`Zonotope.isFullDim_iff` read through `finrank`. At `Vec ℝ n` the dimension is `n`.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the rank is the full dimension iff `Z` has interior
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.rank_eq_finrank_iff (Z : Zonotope α) : -- --- CONCL ---
    Z.rank = Module.finrank ℝ α ↔ (interior Z.construct).Nonempty := by -- --- PROOF ---
  rw [Zonotope.isFullDim_iff]
  constructor
  · exact Submodule.eq_top_of_finrank_eq
  · intro h
    unfold Zonotope.rank
    rw [h, finrank_top]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
