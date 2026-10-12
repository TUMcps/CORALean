import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import Mathlib.Algebra.BigOperators.Fin

/-!
# `PolyZonotope.addedTerms`, over a floating-point scalar

CORA's `@polyZonotope/addedTermsHessian` first step: the weighted sum `∑ᵢ lᵢ · pZᵢ` of the
dimensions of an `n`-dimensional polynomial zonotope as a one-dimensional one (a vector of length
`1`, where the exact layer has the scalar), one new factor `lᵢ` per dimension.
The generators are the original's entries, copied, so nothing is rounded and the error box is
the point `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre's column and every generator's `i`-th entry, times the new factor `lᵢ`. -/
def PolyZonotope.addedTerms (pZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 1 where
  p := pZ.p + n
  h := n * (pZ.h + 1)
  q := 0
  c := fun _ => zero
  G := fun idx _ => (Fin.cons pZ.c pZ.G : Fin (pZ.h + 1) → Vec 𝕋 n)
    (finProdFinEquiv.symm idx).2 (finProdFinEquiv.symm idx).1
  E := fun k idx => Fin.addCases (fun k' => PolyZonotope.extE pZ k' (finProdFinEquiv.symm idx).2)
    (fun j => if j = (finProdFinEquiv.symm idx).1 then 1 else 0) k
  GI := Fin.elim0
  err := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
