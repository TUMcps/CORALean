module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.HalfScaledCost
public import CORALean.Global.Cost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.ComapCost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.IntersectionCost

@[expose] public section

/-!
# `ConZonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`:

* the center `(1/2) • (c₁ + c₂)` and the fresh generator `(1/2) • (c₁ - c₂)`:
  `4 * n`, as in `Zonotope.linCombCost`, and `n * (h₁ + h₂ + 2)` writes for the result's center
  and generators;
* the two `domain`s, a unit box intersected with `P`: `2 * hᵢ + mᵢ` inequality and `meᵢ` equality
  rows of `hᵢ` coefficients, written (box rows, then the concatenation), rows dense;
* the `comap`s along block embeddings write each row at `d = h₁ + h₂ + 1` coefficients;
* negating the parameter functional `blockLast` is `d` negations;
* each domain goes through `halfScaled` over the `d` coefficients, at `HPolytope.halfScaledCost`;
* the final `intersection` writes the rows of both.

The generator blocks are concatenated and not paired, so unlike `Zonotope` the count carries the
constraint sizes `mᵢ`, `meᵢ`, which is what a constrained zonotope's hull pays for them.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.linComb` costs at `Vec ℝ n`, operands of `hᵢ` generators, `mᵢ`
inequality and `meᵢ` equality rows: the zonotope's arithmetic and writes, the two `domain`s, the
two `comap`s, the two `halfScaled`s and the `intersection`. -/
def ConZonotope.linCombCost (n h₁ m₁ me₁ h₂ m₂ me₂ : ℕ) : Cost :=
  ⟨4 * n + (h₁ + h₂ + 1) + n * (h₁ + h₂ + 2)⟩ +
    ⟨(2 * h₁ + m₁ + me₁) * (h₁ + 1) + 2 * h₁ * (h₁ + 1)⟩ +
    ⟨(2 * h₂ + m₂ + me₂) * (h₂ + 1) + 2 * h₂ * (h₂ + 1)⟩ +
    HPolytope.comapCost (2 * h₁ + m₁) me₁ ⟨h₁ + h₂ + 2⟩ +
    HPolytope.comapCost (2 * h₂ + m₂) me₂ ⟨h₁ + h₂ + 2⟩ +
    HPolytope.halfScaledCost (2 * h₁ + m₁) me₁ (h₁ + h₂ + 1) +
    HPolytope.halfScaledCost (2 * h₂ + m₂) me₂ (h₁ + h₂ + 1) +
    HPolytope.intersectionCost (h₁ + h₂ + 1) (2 * h₁ + m₁) (2 * h₂ + m₂) me₁ me₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
