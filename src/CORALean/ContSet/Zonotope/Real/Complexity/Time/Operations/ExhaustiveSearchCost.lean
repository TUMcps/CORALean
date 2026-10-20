module

public import CORALean.Global.Cost
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Zonotope.exhaustiveSearchCost`

Asserted, not proved, as [1, Prop. 10]'s proof counts it: an exhaustive search for the best `n` of
`p` generators builds the `C(p, n)` parallelotopes of [1, Prop. 8], each at `2 * p` (one `Γ⁻¹ g`
per generator, computed and written), then sorts their `C(p, n)` indices. `Zonotope.methodC`
searches a shortlist instead, at [1, Prop. 11]'s cost.

## [1, Prop. 10]: the exhaustive search is `O(C(p, n) · p)`

The sort's `log₂ C(p, n)` is at most `p`, so everything is at most `4 C(p, n) p` once `p ≥ 1`.

## Inputs
* `n` – dimension
* `p` – generator count

## Output
* cost of enumerating, transforming and sorting all parallelotopes

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the exhaustive search of [1, Prop. 10] costs at `n` of `p` generators:
`C(p, n)` parallelotopes at `p` generators each, every one transformed and written, and a sort
of their `C(p, n)` indices. -/
def Zonotope.exhaustiveSearchCost (n p : ℕ) : Cost :=
  ⟨p.choose n * (2 * p)⟩ + Cost.sort (p.choose n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
