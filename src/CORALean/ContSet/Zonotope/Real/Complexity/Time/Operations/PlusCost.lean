module

public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two centers, `n` additions at `Vec ℝ n`,
and concatenates the generator blocks. The concatenation computes nothing but writes every
generator entry, so the result's `n * (1 + h₁ + h₂)` scalars are the writes, and the operands'
generator counts enter: a bound that left them out would be wrong for a long sum of long
operands.

`Complexity/Space/Plus.lean` is the other half and the other kind of claim: how large
the *result* is, which is `rfl` against the definition.

## Inputs
* `n` – dimension
* `h₁` – first generator count
* `h₂` – second generator count

## Output
* `n` additions plus `n(1+h₁+h₂)` writes
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.plus` costs at `Vec ℝ n` on `h₁` and `h₂` generators: `n` additions for the
center and `n * (1 + h₁ + h₂)` writes for the result. -/
def Zonotope.plusCost (n h₁ h₂ : ℕ) : Cost := ⟨n + n * (1 + h₁ + h₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
