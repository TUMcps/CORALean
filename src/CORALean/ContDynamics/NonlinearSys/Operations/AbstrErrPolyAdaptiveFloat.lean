module

public import CORALean.ContDynamics.NonlinearSys.Operations.HessCenterTable
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `priv_abstractionError_adaptive` at `'poly'`, tensor order 3, repaired, in floats

CORA's `VerrorDyn` for the region `Rmax` (absolute) and the differences `Rdiff`: the three
second-order products carrying a difference `d` of `Zdiff` (`quadMapMixed(Zdelta, Zdiff)`,
`quadMapMixed(Zdiff, Zdelta)` and `quadMap(Zdiff)`), and the Hessian box over `Rmax` joined with
`p.x`, less `H` at `p`, in place of CORA's third derivative (zero together for a quadratic field).

## Inputs
* `fm` – float Hessian model
* `A` – state matrix
* `B` – input matrix
* `xs` – linearization point
* `Rmax` – region
* `Zdelta` – zonotope of the start set with the input
* `Rdiff` – differences over the step
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision

## Output
* the abstraction error zonotope
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

/-- `VerrorDyn` of `priv_abstractionError_adaptive` at `'poly'`, tensor order 3: the three
second-order products carrying a difference `d` of `Zdiff`, and the Hessian box over `Rmax` joined
with `p.x`, less `H` at `p`, in place of CORA's third derivative (zero together for quadratic). -/
def NonlinearSys.FloatHessModel.abstrErrPolyAdaptiveFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Rmax : Zonotope (Vec 𝕋 n))
    (Zdelta : Zonotope (Vec 𝕋 (n + m))) (Rdiff : PolyZonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (redFactor : 𝕋) (p : ℕ) : Zonotope (Vec 𝕋 n) :=
  let us := U.c                                                     -- p.u
  let X : Interval (Vec 𝕋 n) := ⟨fun i => minimum (Rmax.interval.inf i) (xs i),  -- totalInt_x,
    fun i => maximum (Rmax.interval.sup i) (xs i)⟩                  --   holding p.x
  let U' : Interval (Vec 𝕋 m) := ⟨fun i => minimum (U.interval.inf i) (us i),     -- totalInt_u,
    fun i => maximum (U.interval.sup i) (us i)⟩                     --   holding p.u
  let rf := sqrtUp p redFactor                                      -- sqrt(options.redFactor)
  let Rred_diff := (Rdiff.zonotopeEven.materialise).reduceAdaptive rf p  -- reduce(zonotope(Rdiff))
  let Zdiff : Zonotope (Vec 𝕋 (n + m)) := Rred_diff.cartProd (Recenter.recenter U)  -- Z_diff
  let Hp := fm.hessCenterTable xs us                                -- H at p, evaluated once
  let Q : Fin n → Mat 𝕋 (n + m) (n + m) := fun i a b => half (Hp i a b)  -- 0.5*H
  let Pδ := Zdelta.ofIndep                                          -- Zdelta
  let Pd := Zdiff.ofIndep                                           -- Z_diff
  let secondOrderDyn := (((PolyZonotope.quadMapMixed Q Pδ Pd).materialise ⊞
    (PolyZonotope.quadMapMixed Q Pd Pδ).materialise) ⊞ (PolyZonotope.quadMap Q Pd).materialise
      ).zonotopeEven.materialise                                    -- the three products with d
  let fmShift : NonlinearSys.FloatHessModel 𝕋 n m :=               -- the Hessian less H at p
    { fm with hess := fun Xb Ub i =>
      Interval.matPlus (fm.hess Xb Ub i) (Interval.point (-Hp i)) }
  let rest := fmShift.hessRemainder A B xs us X U'                  -- |H(X) - H| and A, B
  ((secondOrderDyn ⊞ rest.zonotope).reduceAdaptive rf p).materialise  -- reduce(VerrorDyn,..)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
