import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.PolyZonotope.Float.Operations.MonoBox
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.jacobianBox`

The interval Jacobian of the dependent point map over a box of factor values: column `k` is the
derivative along factor `k`, `Σₗ E[k,l] Gₗ α^{Eˡ - eₖ}`, as `aux_funHanJacobian` of
`@polyZonotope/contains_` builds it (`G(:,ind)·diag(E(i,ind))` and the lowered exponents) and
evaluates it on an interval. The coefficients `E[k,l] Gₗ` are rounded both ways into an interval
matrix, the monomials come from `monoBox`, and `Interval.mtimesIntervalMat` multiplies the two.

`innerApproxImage` differentiates `aux_funcPoly` symbolically instead (`jacobian`,
`matlabFunction`), which yields the same derivative written in another form; an interval
evaluation of another form encloses the same values, possibly more tightly.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An interval matrix holding the Jacobian of the dependent point at every factor vector of the
box `X`. -/
def PolyZonotope.jacobianBox (pZ : PolyZonotope (Vec 𝕋 n)) (X : Interval (Vec 𝕋 pZ.p)) :
    Interval (Mat 𝕋 n pZ.p) :=
  -- the exponents with factor `k` lowered by one
  let Ek : Fin pZ.p → Fin pZ.p → Fin pZ.h → ℕ :=
    fun k k' l => if k' = k then pZ.E k l - 1 else pZ.E k' l
  -- the coefficients `E[k,l] Gₗ`, rounded both ways
  let Ck : Fin pZ.p → Interval (Mat 𝕋 n pZ.h) :=
    fun k => ⟨fun i l => nsmulDown (pZ.E k l) (pZ.G l i), fun i l => nsmulUp (pZ.E k l) (pZ.G l i)⟩
  -- column `k`, the derivative along factor `k`
  let col : Fin pZ.p → Interval (Vec 𝕋 n) :=
    fun k => Interval.mtimesIntervalMat (Ck k) (PolyZonotope.monoBox (Ek k) X)
  Interval.materialiseMat ⟨fun i k => (col k).inf i, fun i k => (col k).sup i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
