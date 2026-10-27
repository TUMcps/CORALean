module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `ConZonotope.reduceCost`

Asserted, not proved, step by step as `Operations/Reduce.lean` runs CORA's algorithm. Compacting
reads every column of `[G; A; Aₑ]` and the right-hand sides, `(n + r + re)(h + 1)` reads. The lift
writes `[c; -bₑ]` and `[G; Aₑ]`, `(n + re)(1 + h)` scalars. Girard's rule on the lifted zonotope is
`Zonotope.reduceGirardCost` in dimension `n + re`. Each inequality row's slack takes an absolute
value and an addition per entry, `2 r (h + 1)`. The result, at most `h + n + re` generators, is
written once, `(n + r + re)(h + n + re + 1)`. No linear program anywhere in it. Below the threshold
only compacting runs, so this bounds every `o` at once.

## Inputs
* `n` – dimension
* `h` – number of generators
* `r` – number of inequalities
* `re` – number of equalities

## Output
* the cost of the order reduction
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.reduce`, at any order, costs at `Vec ℝ n` on `h` generators and a constraint
polytope of `r` inequality and `re` equality rows: compacting, the lift, Girard's rule on the lifted
zonotope, the inequality rows' slacks and the writes of the result. -/
def ConZonotope.reduceCost (n h r re : ℕ) : Cost :=
  Zonotope.reduceGirardCost (n + re) h + ⟨(n + r + re) * (h + 1) + (n + re) * (1 + h)
    + 2 * r * (h + 1) + (n + r + re) * (h + n + re + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
