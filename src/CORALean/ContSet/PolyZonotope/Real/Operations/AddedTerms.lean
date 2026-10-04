import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import Mathlib.Algebra.BigOperators.Fin

/-!
# `PolyZonotope.addedTerms`

The first step of CORA's `@polyZonotope/addedTermsHessian`: the weighted sum `∑ᵢ lᵢ · pZᵢ`
over the dimensions of an `n`-dimensional polynomial zonotope, one new factor `lᵢ` per
dimension (exponent `1` on exactly the terms of dimension `i`), as a one-dimensional
polynomial zonotope. Identifiers are positional: the factors of `pZ` are `Fin p`, the weights
`Fin n`, and the sum's factors `Fin (p + n)`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- For each dimension `i` the centre and every generator's `i`-th entry, times the new factor
`lᵢ`; the centre's column has the all-zero exponent. -/
def PolyZonotope.addedTerms (pZ : PolyZonotope (Vec ℝ n)) : PolyZonotope ℝ where
  p := pZ.p + n
  h := n * (pZ.h + 1)
  q := 0
  c := 0
  G := fun idx => (Fin.cons pZ.c pZ.G : Fin (pZ.h + 1) → Vec ℝ n)
    (finProdFinEquiv.symm idx).2 (finProdFinEquiv.symm idx).1
  E := fun k idx => Fin.addCases (fun k' => pZ.extE k' (finProdFinEquiv.symm idx).2)
    (fun j => if j = (finProdFinEquiv.symm idx).1 then 1 else 0) k
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
