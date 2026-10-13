import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.NormMag
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Global.Float.BilinUp

/-!
# The abstraction error of a conservative polynomialization, in floats

CORA's `priv_precompStatError` and `priv_abstrerr_poly`, [1, Sec. 4.1], in `𝕋`. A state
of the step is `x = x(0) + δ` with `x(0) - x✱ ∈ Rdelta` and `δ ∈ Rdiff`, so at
`z₀ = (x(0) - x✱, 0)` and `δz = (δ, u - u✱)` the second-order term splits into
`errorStat = ½ quadMap(Zdelta, H(z✱))`, kept as the polynomial it is over the start
set's factors and only then enclosed, and the products carrying a `δz`. Those are
`error_secondOrder_dyn`, boxed here as `abstrerr_lin` boxes, and with them what the
Hessian box over the step leaves of `H(z✱)`: CORA bounds that by the third-order
tensor, which the model does not carry, so this is the second-order Lagrange form.

`A`, `B` are centres, not the Jacobian, so `hessRemainder`'s first-order slack is
added. `Zdelta`'s input block is `0`, CORA's `Ustat`, so `errorStat` needs the state
block of `H(z✱)` alone.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `½ quadMap(Rdelta, H(z✱)) ⊕ ([J(z✱)] - [A B])(X × U - z✱) ⊕ [-l, l]`, `l` bounding
over `X × U` the products of the Hessian box that carry a difference in `Rdiff`. -/
def NonlinearSys.FloatHessModel.abstrErrPolyFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) (Rdelta Rdiff : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  -- priv_precompStatError: half the Hessian at `z✱`, on the start set
  let Hs := fun i => (fm.hess (Interval.point xs) (Interval.point us) i).centreMat  -- H(z✱)
  let Q : Fin n → Mat 𝕋 n n := fun i j k => half (Hs i (Fin.castAdd m j) (Fin.castAdd m k))
  let errorStat := (PolyZonotope.quadMap Q Rdelta.polyZonotope).zonotope    -- 0.5*quadMap(Zdelta,H)
  -- the first-order slack of linearizing at centres
  let Jx := fm.jacX (Interval.point xs) (Interval.point us)          -- [∂f/∂x (z✱)]
  let Ju := fm.jacU (Interval.point xs) (Interval.point us)          -- [∂f/∂u (z✱)]
  let ΔJx := Interval.matPlus Jx (Interval.point fun i j => neg (A i j))  -- [∂f/∂x (z✱)] - A
  let ΔJu := Interval.matPlus Ju (Interval.point fun i j => neg (B i j))  -- [∂f/∂u (z✱)] - B
  let IHx := Interval.plus X (Interval.point fun i => neg (xs i))   -- X - x✱
  let IHu := Interval.plus U (Interval.point fun i => neg (us i))   -- du = U - u✱
  -- priv_abstrerr_poly: the products carrying a difference, and the Hessian's spread
  let dδ : Vec 𝕋 (n + m) := Fin.append Rdelta.interval.normMag fun _ => zero  -- |Zdelta|
  let dd : Vec 𝕋 (n + m) := Fin.append Rdiff.interval.normMag IHu.normMag    -- |Z_diff|
  let H := fm.hess X U                                              -- [H] over the step
  let Habs := fun i j k => maximum (absolute ((H i).inf j k)) (absolute ((H i).sup j k))
  let Hdev := fun i j k =>                                          -- |[H] - H(z✱)|
    maximum (subUp ((H i).sup j k) (Hs i j k)) (subUp (Hs i j k) ((H i).inf j k))
  let l : Vec 𝕋 n := fun i => half (addUp                          -- 0.5*(... + quadMap(Z_diff))
    (addUp (bilinUp dδ (Hdev i) dδ) (bilinUp dδ (Habs i) dd))
    (addUp (bilinUp dd (Habs i) dδ) (bilinUp dd (Habs i) dd)))
  errorStat ⊞ (Interval.plus (Interval.plus (Interval.mtimesIntervalMat ΔJx IHx)
    (Interval.mtimesIntervalMat ΔJu IHu)) ⟨fun i => neg (l i), l⟩).zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
