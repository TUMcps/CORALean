module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost

@[expose] public section

/-!
# `Zonotope.reduceCombastelCost`

Asserted, not proved, by reading `Operations/ReduceCombastel.lean`. The metric is
a squared length, `n` products and `n - 1` additions per generator, bounded by
`2 * n`; then the `h` keys are sorted and `reduceBy` absorbs a block of at most
`h`. Girard's metric costs `4 * n + 2` per generator, so this is the cheaper
rule by a constant factor, not an order.

No order argument: below order `o` the operation is the identity and costs
nothing, and above it the absorbed block is at most `h` wide.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceCombastel` costs at `Vec ℝ n` on `h` generators. -/
def Zonotope.reduceCombastelCost (n h : ℕ) : Cost :=
  ⟨h * (2 * n)⟩ + Cost.sort h + Zonotope.reduceByCost n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
