import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
import CORALean.Global.Cost

/-!
# `ConZonotope.intersectionCost`

Asserted, not proved: `Operations/Intersection.lean` keeps the first centre and
generator block, pads the second block with zeros, builds the polytope as in
`plus` (free) and adds the equalities `G₁ β₁ - G₂ β₂ = c₂ - c₁`. Assembling
`agreeMat` negates the `n * h₂` entries of the second block, and the right-hand
side is `n` subtractions; `HPolytope.eqs` wraps the rows as functionals and is
free. No linear program is solved: emptiness is not decided here.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.intersection` costs at `Vec ℝ n` and `h₂` generators in the
second operand: `n * h₂` negations and `n` subtractions. -/
def ConZonotope.intersectionCost (n h₂ : ℕ) : Cost := ⟨n * (h₂ + 1)⟩

/-- Monotone in the second operand's generator count, so a bound on its size
gives a bound on the cost. -/
theorem ConZonotope.intersectionCost_mono {h₂ h₂' : ℕ} (n : ℕ) (hh : h₂ ≤ h₂') :
    ConZonotope.intersectionCost n h₂ ≤ ConZonotope.intersectionCost n h₂' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
