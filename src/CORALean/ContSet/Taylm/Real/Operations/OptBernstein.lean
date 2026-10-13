import CORALean.ContSet.Taylm.Real.Operations.BernsteinCoeff
import CORALean.ContSet.Taylm.Real.Operations.BernsteinDegree

/-!
# `Taylm.optBernstein`

CORA's `optBernstein` [2]: the range of the polynomial part over `[-1, 1]ⁿ` as the least and
greatest of its Bernstein coefficients (`poly2bernstein` [1], at the degree `n = max(max(E))`),
plus the remainder interval. Written as a pair (lower, upper), as `Taylm.bounds`.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
* [2] `contSet/@taylm/optBernstein.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `optBernstein`: `interval(min(min(B)), max(max(B))) + obj.remainder`. -/
noncomputable def Taylm.optBernstein (T : Taylm n) : ℝ × ℝ :=
  let N := T.bernsteinDegree                                         -- n = max(max(E))
  let B := Taylm.bernsteinCoeff T.terms N                           -- poly2bernstein(G, E, dom)
  (Finset.univ.inf' ⟨fun _ => 0, Finset.mem_univ _⟩ B + T.remInf,    -- min(min(B)) + remainder
   Finset.univ.sup' ⟨fun _ => 0, Finset.mem_univ _⟩ B + T.remSup)    -- max(max(B)) + remainder

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
