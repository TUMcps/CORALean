module

public import CORALean.ContDynamics.NonlinearSys.Operations.HessCenterTable

@[expose] public section

/-!
# The Hessian table holds the centers of the Hessian boxes

`hessCenterTable` tabulates, once, the centers of the model's Hessian boxes at the point intervals
`(x✱, u✱)`; the function it returns is the function of centers it tabulates.

## Inputs
* `fm` – float Hessian model
* `xs` – state point
* `us` – input point

## Hypotheses
* none

## Conclusion
* the table is the function of centers
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.FloatHessModel.hessCenterTable_eq (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) : -- --- CONCL ---
    fm.hessCenterTable xs us
      = fun i =>
        (fm.hess (Interval.point xs) (Interval.point us) i).centerMat := by -- --- PROOF ---
  funext i a b
  simp [NonlinearSys.FloatHessModel.hessCenterTable]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
