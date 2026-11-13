module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyLoopFloat
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceCora

@[expose] public section

/-!
# One step of CORA's `linReach` from a polynomial zonotope, with `post`

`linReachPolyLoopFloat` followed by CORA's `post`, which reduces both sets to order `options.ρ`
(`PolyZonotope.reduceCora`). The result is the sets of the step and its error, then each reduced
set with the indices of the dependent generators it kept, the identifiers of the factors it still
reads.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error, CORA's `1.1`
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `order` – the order of equal exponent columns (CORA's hash order)

## Output
* the sets of the step and its error, and the two reduced sets with their kept indices, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linReachPolyLoopFloat` followed by CORA's `post`, which reduces both sets to order
`options.ρ`: the sets of the step and its error, then each reduced set with the indices of the
dependent generators it kept (the identifiers of the factors it still reads). -/
def NonlinearSys.FloatHessModel.linReachPolyFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (R : PolyZonotope (Vec 𝕋 n)) (abstrerr : Vec 𝕋 n) (maxError : Option (Vec 𝕋 n) := none)
    (order : ℕ → Array (Array ℕ) → Array ℕ) :
    Option ((PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) × Vec 𝕋 n) ×
      (PolyZonotope (Vec 𝕋 n) × List ℕ) × (PolyZonotope (Vec 𝕋 n) × List ℕ)) := do
  let S ← fm.linReachPolyLoopFloat U options enlarge fuel R abstrerr maxError order
  pure (S, S.1.reduceCora options.ρ order, S.2.1.reduceCora options.ρ order)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
