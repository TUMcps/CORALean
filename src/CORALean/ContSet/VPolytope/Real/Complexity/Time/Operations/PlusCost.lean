module

public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.plusCost`

Asserted, not proved: `Operations/Plus.lean` pairs every vertex of one operand
with every vertex of the other and adds the pair, `n` additions at `Vec ℝ n`
each — `k₁ * k₂` pairs in all, `finProdFinEquiv` being index work — and writes each
sum, `n` entries.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `VPolytope.plus` costs at `Vec ℝ n` on `k₁`, `k₂` vertices: `n` additions per pair of
vertices, and as many writes. -/
def VPolytope.plusCost (n k₁ k₂ : ℕ) : Cost := ⟨2 * (n * (k₁ * k₂))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
