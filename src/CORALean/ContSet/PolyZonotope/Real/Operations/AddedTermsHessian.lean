module

public import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTerms
public import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian

@[expose] public section

/-!
# `PolyZonotope.addedTermsHessian`

CORA's `@polyZonotope/addedTermsHessian`: the Hessian of `addedTerms`, as the point of its
second derivatives (`jacobian` twice) at the factor vector `a` and the weights `l`. CORA splits
the factors of `pZ` into `id_diff` (the variables of the Hessian) and `id_param` (held fixed);
here the matrix is over all pairs of factors and a caller reads the entries on `id_diff`.
CORA drops the terms of degree `≤ 1` in the differentiated factors and fills the lower
triangle by symmetry; both leave the value unchanged and are not modelled. The tolerance `tol`
is `0`, and the structure matrix `H_str` is not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `H(a, l)ⱼₖ`: the second derivative of `addedTerms`, along factor `k` and then `j`. -/
def PolyZonotope.addedTermsHessian (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ)
    (l : Fin n → ℝ) : Matrix (Fin pZ.p) (Fin pZ.p) ℝ :=
  Matrix.of fun j k =>
    ((pZ.addedTerms.jacobian (Fin.castAdd n k)).jacobian (Fin.castAdd n j)).point
      (Fin.append a l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
