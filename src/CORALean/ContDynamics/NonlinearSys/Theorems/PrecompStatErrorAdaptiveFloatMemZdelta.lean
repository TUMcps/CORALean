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
# `precompStatErrorAdaptiveFloat` holds the start set with the input

The point `a` of the start set with an input `μ` of `U - u✱` is in `Zdelta`, the Cartesian product
of the reduced start set and the recentered input.

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
* the point with the input is in `Zdelta`
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

/-- The point of the start set with the input is in `Zdelta`. -/
theorem NonlinearSys.FloatHessModel.precompStatErrorAdaptiveFloat_mem_Zdelta
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (xs : Vec 𝕋 n) (U : Zonotope (Vec 𝕋 m))
    (redFactor : 𝕋) (p : ℕ) (Rdelta : PolyZonotope (Vec 𝕋 n)) {a : Vec ℝ n} {μ : Vec ℝ m}
    (ha : a ∈ Rdelta.toSet) (hμ : μ ∈ (Recenter.recenter U).toSet) : -- --- CONCL ---
    Fin.append a μ ∈
      (fm.precompStatErrorAdaptiveFloat xs U redFactor p Rdelta).2.toSet := by -- --- PROOF ---
  unfold NonlinearSys.FloatHessModel.precompStatErrorAdaptiveFloat
  dsimp only
  rw [Zonotope.materialise_eq, Zonotope.cartProd_exact]
  refine ⟨(a, μ), ⟨?_, hμ⟩, rfl⟩
  rw [Zonotope.materialise_eq]
  exact Zonotope.reduceAdaptive_outer _ _ _ (PolyZonotope.zonotopeEven_contains _ ha)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
