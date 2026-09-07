import CORALean.ContSet.PolyZonotope.Real.Cost.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

/-!
# `PolyZonotope.mulCost`

Asserted, not proved: `Operations/Mul.lean` is `bilin` at the entrywise
product, which is `n` multiplications at `Vec ℝ n` and nothing else, so the
whole count is `bilinCost` at `⟨n⟩`.

Quadratic in the generator counts, and that is the operation's own doing rather
than the model's: `Complexity/Bilin.lean` proves the result carries
`(h₁+1)(h₂+1)` generators, and each of them is computed. A caller who repeats
`mul` to reach a higher order pays this at the previous product's count, which
is why `compact` and `reduce` sit between the factors in practice.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.mul` costs at `Vec ℝ n` over `p` shared factors: `n`
multiplications and `p` exponent additions per pair of extended columns. -/
def PolyZonotope.mulCost (n p h₁ h₂ : ℕ) : Cost := PolyZonotope.bilinCost ⟨n⟩ p h₁ h₂

/-- Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem PolyZonotope.mulCost_mono {h₁ h₁' h₂ h₂' : ℕ} (n p : ℕ)
    (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.mulCost n p h₁ h₂ ≤ PolyZonotope.mulCost n p h₁' h₂' :=
  PolyZonotope.bilinCost_mono _ le_rfl h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
