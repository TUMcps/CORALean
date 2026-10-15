module

public import CORALean.ContSet.VPolytope.Real.Operations.LinComb
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.linCombCost`

Asserted, not proved, and no longer zero: `Operations/LinComb.lean` is `Fin.append` on the two
vertex lists. No fresh vertex is computed, unlike a zonotope's `linComb`, but the result lists
`k₁ + k₂` vertices of `n` entries, and each entry is a write.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `VPolytope.linComb` costs at `Vec ℝ n` on `k₁` and `k₂` vertices: one write for each of
the `n * (k₁ + k₂)` entries of the concatenated vertex list. -/
def VPolytope.linCombCost (n k₁ k₂ : ℕ) : Cost := ⟨n * (k₁ + k₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
