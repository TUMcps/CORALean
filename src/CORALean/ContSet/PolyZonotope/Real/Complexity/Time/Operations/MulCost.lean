module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.BilinCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

@[expose] public section

/-!
# `PolyZonotope.mulCost`

Asserted, not proved: `Operations/Mul.lean` is `bilin` at the entrywise
product, which is `n` multiplications at `Vec ℝ n`, each written, so the whole
count is `bilinCost` at `⟨2 * n⟩`.

Quadratic in the generator counts, and that is the operation's own doing rather
than the model's: `Complexity/Space/Theorems/Bilin*.lean` proves the result carries
`(h₁+1)(h₂+1)` generators, and each of them is computed. A caller who repeats
`mul` to reach a higher order pays this at the previous product's count, which
is why `compact` and `reduce` sit between the factors in practice.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.mul` costs at `Vec ℝ n` over `p` shared factors: `n` multiplications, `n`
writes and `p` exponent additions with `p` writes per pair of extended columns, and `n` writes
for the zero center. -/
def PolyZonotope.mulCost (n p h₁ h₂ : ℕ) : Cost := PolyZonotope.bilinCost ⟨2 * n⟩ n p h₁ h₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
