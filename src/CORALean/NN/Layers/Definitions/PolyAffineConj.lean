import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.Global.Float.Instances.Real.Instances

/-!
# A polynomial relaxation carried along an affine conjugation, over ℝ

`g t = a f (b t) + d` inherits a polynomial relaxation of `f` at every order, not only the
affine one: the monomial basis is closed under scaling its argument, so the conjugation only
reweights the coefficients — `b` folds into the monomials one power at a time, `a` multiplies
every coefficient once, `d` is the constant's shift — and the error scales by `a`. Nothing about
the fit or the error bound is redone, which is what makes tanh cost a line. Over ℝ, where the
reweighting is exact; no machine scalar stores a polynomial tanh relaxation.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polynomial relaxation of `f` transported along `g t = a f (b t) + d`. -/
noncomputable def PolyRelaxation.ofAffineConj {n : ℕ} (P : CORALean.PolyRelaxation ℝ n)
    (a b d : ℝ) : CORALean.PolyRelaxation ℝ n where
  coeffs l u := shiftConst (scaleCoeffs (P.coeffs (b * l) (b * u)) a b) d
  error l u := a * P.error (b * l) (b * u)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
