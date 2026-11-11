module

public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatErrorAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessCenterTableEq
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `precompStatErrorAdaptiveFloat` holds the static error

The static error `½ zᵀ H✱ z` at a point `a` of the start set and an input `μ` of `U - u✱` is in
`Vstat`: the reductions and `quadMap` only enlarge, and `(a, μ)` is in `cartProd(Rred, U)`.

## Inputs
* `fm` – float Hessian model
* `xs` – linearization point
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision
* `Rdelta` – start set less the linearization point
* `a` – point of the start set
* `μ` – input less the center

## Hypotheses
* `ha` – the point is in the start set
* `hμ` – the input is in `U - u✱`

## Conclusion
* the static error is in `Vstat`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The static error at a point of the start set and an input is in `Vstat`. -/
theorem NonlinearSys.FloatHessModel.precompStatErrorAdaptiveFloat_mem_stat
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (xs : Vec 𝕋 n) (U : Zonotope (Vec 𝕋 m))
    (redFactor : 𝕋) (p : ℕ) (Rdelta : PolyZonotope (Vec 𝕋 n)) {a : Vec ℝ n} {μ : Vec ℝ m}
    (ha : a ∈ Rdelta.toSet) (hμ : μ ∈ (Recenter.recenter U).toSet) : -- --- CONCL ---
    (fun i => Fin.append a μ ⬝ᵥ (Scalar.toRealMat
      ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ Fin.append a μ) / 2)
      ∈ (fm.precompStatErrorAdaptiveFloat xs U redFactor p Rdelta).1.toSet := by -- --- PROOF ---
  -- the static error is the quadratic map at `½ H✱` of the point with the input
  unfold NonlinearSys.FloatHessModel.precompStatErrorAdaptiveFloat
  dsimp only
  simp only [NonlinearSys.FloatHessModel.hessCenterTable_eq]
  refine PolyZonotope.reduceAdaptive_outer _ _ _ ?_
  rw [PolyZonotope.materialise_eq]
  -- the point with the input is in the Cartesian product
  have hz : Fin.append a μ ∈ ((Rdelta.reduceAdaptive (sqrtUp p redFactor) p).cartProd
      (Recenter.recenter U).ofIndep).toSet := by
    rw [PolyZonotope.cartProd_exact]
    exact ⟨(a, μ), ⟨PolyZonotope.reduceAdaptive_outer _ _ _ ha, Zonotope.ofIndep_outer _ hμ⟩, rfl⟩
  -- the guarantee of the quadratic map, then its matrices halved exactly
  have hq := PolyZonotope.quadMap_outer
    (fun i a b => half ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat a b)) _
    (Set.mem_image_of_mem _ hz)
  convert hq using 1
  funext i
  simp only [Real.PolyZonotope.quadEval]
  have hhalf : (toRealMat fun a b => half ((fm.hess (Interval.point xs) (Interval.point U.c)
      i).centerMat a b)) = (1 / 2 : ℝ) • Scalar.toRealMat
        ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) := by
    funext a b
    rw [Matrix.smul_apply, Scalar.toRealMat_apply, toRealMat, toReal_half, smul_eq_mul]
    change toReal ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat a b) / 2
      = 1 / 2 * toReal ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat a b)
    ring
  rw [hhalf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
