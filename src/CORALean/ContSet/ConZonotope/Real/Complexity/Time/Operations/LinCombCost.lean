module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.HalfScaledCost
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConZonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`:

* the center `(1/2) • (c₁ + c₂)` and the fresh generator `(1/2) • (c₁ - c₂)`:
  `4 * n`, as in `Zonotope.linCombCost`;
* the two `domain`s are a unit box intersected with `P`, whose rows concatenate
  (free), so they carry `2 * hᵢ + mᵢ` inequality rows and `meᵢ` equality rows;
* the `comap`s along block embeddings are free (`HPolytope.comapCost`'s file);
* negating the parameter functional `blockLast` is `d` negations;
* each domain goes through `halfScaled` over the `d = h₁ + h₂ + 1` coefficients,
  at `HPolytope.halfScaledCost`, rows read dense;
* the final `intersection` is free.

The generator blocks are concatenated and not paired, so unlike `Zonotope` the
count carries the constraint sizes `mᵢ`, `meᵢ`, which is what a constrained
zonotope's hull pays for keeping them exact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.linComb` costs at `Vec ℝ n`, operands of `hᵢ` generators,
`mᵢ` inequality and `meᵢ` equality rows. -/
def ConZonotope.linCombCost (n h₁ m₁ me₁ h₂ m₂ me₂ : ℕ) : Cost :=
  ⟨4 * n + (h₁ + h₂ + 1)⟩ + HPolytope.halfScaledCost (2 * h₁ + m₁) me₁ (h₁ + h₂ + 1) +
    HPolytope.halfScaledCost (2 * h₂ + m₂) me₂ (h₁ + h₂ + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
