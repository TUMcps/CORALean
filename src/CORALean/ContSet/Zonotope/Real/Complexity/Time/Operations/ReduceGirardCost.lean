module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

@[expose] public section

/-!
# `Zonotope.reduceGirardCost`

Asserted, not proved, by reading `Operations/ReduceGirard.lean`. Girard's
metric on one generator is `n` absolute values and `n - 1` additions for
`‖g‖₁`, `n` more and `n` comparisons for the `max` fold, one subtraction and
one negation for the descending sort key: at most `4 * n + 2` each. Then the
`h` keys are sorted, and `reduceBy` absorbs a block of at most `h`.

No order argument: below order `o` the operation is the identity and costs
nothing, and above it the absorbed block is at most `h` wide either way, so
this bounds every `o` at once.

`reduceBy` is charged at `h` kept and `h` absorbed generators, each at most `h`, and writes its
own result; the `else` branch returns the operand and writes at most the same `n * (1 + h)`.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceGirard`, and so `Zonotope.reduce`, costs at `Vec ℝ n` on `h` generators:
the metrics, the sort, and the block `reduceBy` writes, at most `h` kept and `h` absorbed. -/
def Zonotope.reduceGirardCost (n h : ℕ) : Cost :=
  ⟨h * (4 * n + 2)⟩ + Cost.sort h + Zonotope.reduceByCost n h h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
