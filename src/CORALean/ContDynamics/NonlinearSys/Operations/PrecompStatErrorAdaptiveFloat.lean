module

public import CORALean.ContDynamics.NonlinearSys.Operations.HessCenterTable
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `priv_precompStatError_adaptive` at `'poly'`, in floats

CORA's static error over the reduced start set: `errorStat = reduce(½ quadMap(cartProd(
reduce(Rdelta,'adaptive'), U), H), 'adaptive')`, kept as a polynomial zonotope over the factors of
`Rdelta`, and `Zdelta`, the zonotope of `Rdelta` (even columns) reduced and paired with `U`.

## Inputs
* `fm` – float Hessian model
* `xs` – linearization point
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision
* `Rdelta` – start set less the linearization point

## Output
* the static error and `Zdelta`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The static error `Vstat` and `Zdelta` of `priv_precompStatError_adaptive`:
`reduce(½ quadMap(cartProd(reduce(Rdelta), U), H))` and the zonotope of `Rdelta` with `U`. -/
def NonlinearSys.FloatHessModel.precompStatErrorAdaptiveFloat
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (xs : Vec 𝕋 n) (U : Zonotope (Vec 𝕋 m))
    (redFactor : 𝕋) (p : ℕ) (Rdelta : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 (n + m)) :=
  let rf := sqrtUp p redFactor                                      -- sqrt(options.redFactor)
  let Rred := Rdelta.reduceAdaptive rf p                            -- reduce(Rdelta,'adaptive')
  let Rdz := (Rdelta.zonotopeEven.materialise).reduceAdaptive rf p  -- reduce(zonotope(Rdelta),..)
  let Hp := fm.hessCenterTable xs U.c                               -- H at p, evaluated once
  let Q : Fin n → Mat 𝕋 (n + m) (n + m) := fun i a b => half (Hp i a b)
  let Z := Rred.cartProd (Recenter.recenter U).ofIndep              -- cartProd(Rred,U)
  let errorSecOrdStat := (PolyZonotope.quadMap Q Z).materialise     -- 0.5*quadMap(Z,H)
  (errorSecOrdStat.reduceAdaptive rf p,                             -- errorStat
    (Rdz.cartProd (Recenter.recenter U)).materialise)               -- Zdelta

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
