module

public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.plusCost`

Asserted, not proved: `Operations/Plus.lean` pairs every vertex of one operand
with every vertex of the other and adds the pair, `n` additions at `Vec ℝ n`
each — `k₁ * k₂` pairs in all, `finProdFinEquiv` being index work and free.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `VPolytope.plus` costs at `Vec ℝ n` on `k₁`, `k₂` vertices: `n`
additions per pair of vertices. -/
def VPolytope.plusCost (n k₁ k₂ : ℕ) : Cost := ⟨n * (k₁ * k₂)⟩

/-- Monotone in both vertex counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem VPolytope.plusCost_mono {k₁ k₁' k₂ k₂' : ℕ} (n : ℕ) (h1 : k₁ ≤ k₁') (h2 : k₂ ≤ k₂') :
    VPolytope.plusCost n k₁ k₂ ≤ VPolytope.plusCost n k₁' k₂' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
