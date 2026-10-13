import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Compact
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

/-!
# `PolyZonotope.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` is `compact` and then
`reduceGirard`, so the count is the two added.

The ranking is priced at the *operand's* counts and not at what compaction
leaves, which is sound because compaction only ever shrinks them:
`Complexity/Space/Compact.lean` proves `compact_h_le` and `compact_q`, and
`reduceGirardCost_mono` turns those into this inequality. Stating it here at
the operand's own sizes is what lets a caller who knows nothing about how many
columns collided still bound the whole operation.

Quadratic in `h`, from the merge and the sorts alike, against a `Zonotope`'s
`reduce` which is quadratic only in the sort — the price of exponent columns
that can repeat.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduce`, at any order, costs at `Vec ℝ n` over `p`
factors, `h` dependent and `q` independent generators. -/
def PolyZonotope.reduceCost (n p h q : ℕ) : Cost :=
  PolyZonotope.compactCost n p h + PolyZonotope.reduceGirardCost n h q

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceCost n p h q ≤ PolyZonotope.reduceCost n p h' q' :=
  Cost.add_le_add (PolyZonotope.compactCost_mono n p hh)
    (PolyZonotope.reduceGirardCost_mono n hh hq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
