module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.CompactCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `PolyZonotope.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` is `compact` and then
`reduceGirard`, so the count is the two added.

The ranking is priced at the *operand's* counts and not at what compaction
leaves, which is sound because compaction only ever shrinks them:
`Complexity/Space/Theorems/CompactHLe.lean` proves `compact_h_le` and `compact_q`, and
`reduceGirardCost_mono` turns those into this inequality. Stating it here at
the operand's own sizes is what lets a caller who knows nothing about how many
columns collided still bound the whole operation.

Quadratic in `h`, from the merge and the sorts alike, against a `Zonotope`'s
`reduce` which is quadratic only in the sort — the price of exponent columns
that can repeat.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduce`, at any order, costs at `Vec ℝ n` over `p` factors, `h` dependent
and `q` independent generators. -/
def PolyZonotope.reduceCost (n p h q : ℕ) : Cost :=
  PolyZonotope.compactCost n p h q + PolyZonotope.reduceGirardCost n p h q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
