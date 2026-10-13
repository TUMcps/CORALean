import CORALean.ContSet.Zonotope.Real.Operations.MethodCBasis
import CORALean.ContSet.Zonotope.Real.Operations.Parallelotope

/-!
# `Zonotope.methodC`: a zonotope reduced to a parallelotope by method C

[1, Sec. 5.4.2]'s method C, the reduction to a parallelotope the paper recommends for the
halfspace conversion: [1, Prop. 8]'s `Γ box(Γ⁻¹Z)` at the `Γ` `methodCBasis` selects,
`κ = 8`, `κ̃ = 3` in the paper's evaluation and `κ = 5` in its numerical example.

CORA's `reduce(Z, 'methC', o)`, `Zonotope.reduceMethC`, is a relative: it boxes only what
Girard's ranking drops, keeps `λ = 1`, and ranks lengths after its own row scaling.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.4.2]: the parallelotope method C encloses `Z` by. -/
noncomputable def Zonotope.methodC (Z : Zonotope (Vec ℝ n)) (κ κ' : ℕ) : Zonotope (Vec ℝ n) :=
  Z.parallelotope (Z.methodCBasis κ κ')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
