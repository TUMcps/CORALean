import CORALean.Global.Cost
import Mathlib.Data.Nat.Choose.Basic

/-!
# `Zonotope.exhaustiveSearchCost`

Asserted, not proved, as [1, Prop. 10]'s proof counts it: an exhaustive search for the
best `n` of `p` generators builds the `C(p, n)` parallelotopes of [1, Prop. 8], each
at `O(p)` with respect to the generators — one `Γ⁻¹ g` per generator, `n` fixed — and
then sorts their `C(p, n)` indices `Θ`. The per-parallelotope `p` is the paper's
reading, with its constant in `n` dropped as the paper drops it.

No search here is priced against a Lean definition: `Zonotope.methodC` searches a
filtered shortlist instead, and its cost is [1, Prop. 11]'s, this one at `p = n + κ`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the exhaustive search of [1, Prop. 10] costs at `n` of `p` generators:
`C(p, n)` parallelotopes at `p` each, and a sort of their `C(p, n)` indices. -/
def Zonotope.exhaustiveSearchCost (n p : ℕ) : Cost :=
  ⟨p.choose n * p⟩ + Cost.sort (p.choose n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
