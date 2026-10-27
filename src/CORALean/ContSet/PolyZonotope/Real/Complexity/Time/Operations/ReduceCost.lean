module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` is `compact` and then `reduceGirard`, so the
count is the two added. The ranking is priced at the *operand's* counts and not at what
compaction leaves, which is sound because compaction only shrinks them
(`Complexity/Space/Theorems/CompactHLe.lean`; `reduceGirardCost_mono` turns that into this
inequality). Quadratic in `h`, from the merge and the sorts alike, against a `Zonotope`'s
`reduce` quadratic only in the sort: the price of exponent columns that can repeat.

## Inputs
* `n` – dimension
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count

## Output
* operation count of compacting and reducing
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- What `PolyZonotope.compact` costs at `Vec ℝ n` over `p` factors, `h` dependent and `q`
independent generators: the pairwise merge, the class sums and the factor scan, and
`n * (1 + h + q) + p * h` writes for the result. -/
@[step_of PolyZonotope.reduceCost]
def PolyZonotope.step_compactCost (n p h q : ℕ) : Cost :=
  ⟨(p + n + 1) * (h * h) + (p + n) * h + (n * (1 + h + q) + p * h)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduce`, at any order, costs at `Vec ℝ n` over `p` factors, `h` dependent
and `q` independent generators. -/
def PolyZonotope.reduceCost (n p h q : ℕ) : Cost :=
  PolyZonotope.step_compactCost n p h q + PolyZonotope.reduceGirardCost n p h q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
