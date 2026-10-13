module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.HalfScaled
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConZonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`:

* the centre `(1/2) • (c₁ + c₂)` and the fresh generator `(1/2) • (c₁ - c₂)`:
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

/-- Monotone in the operands' sizes, so a bound on them gives a bound on the cost. -/
theorem ConZonotope.linCombCost_mono {n h₁ h₁' m₁ m₁' me₁ me₁' h₂ h₂' m₂ m₂' me₂ me₂' : ℕ}
    (hh₁ : h₁ ≤ h₁') (hm₁ : m₁ ≤ m₁') (hme₁ : me₁ ≤ me₁')
    (hh₂ : h₂ ≤ h₂') (hm₂ : m₂ ≤ m₂') (hme₂ : me₂ ≤ me₂') :
    ConZonotope.linCombCost n h₁ m₁ me₁ h₂ m₂ me₂ ≤
      ConZonotope.linCombCost n h₁' m₁' me₁' h₂' m₂' me₂' := by -- --- PROOF ---
  have hd : h₁ + h₂ + 1 ≤ h₁' + h₂' + 1 := by omega
  have a := HPolytope.halfScaledCost_mono (by omega : 2 * h₁ + m₁ ≤ 2 * h₁' + m₁') hme₁ hd
  have b := HPolytope.halfScaledCost_mono (by omega : 2 * h₂ + m₂ ≤ 2 * h₂' + m₂') hme₂ hd
  simp only [ConZonotope.linCombCost, Cost.le_iff, Cost.ops_add] at a b ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
