module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
public import CORALean.ContSet.Interval.Float.Operations.CenterMat

@[expose] public section

/-!
# The centers of the Hessian boxes at a point, as a table

`H` at the linearization point `p`: the center of each box of the model's Hessian over the point
intervals `(x✱, u✱)`. The model's function evaluates its derivative trees at every call, so the
centers are tabulated once and the returned function reads the table.

## Inputs
* `fm` – float Hessian model
* `xs` – state point
* `us` – input point

## Output
* the Hessian centers, one matrix per state component
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

/-- `H(i)` at `(xs, us)`: entry `(a, b)` of component `i`, read from a table evaluated once. -/
def NonlinearSys.FloatHessModel.hessCenterTable (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) : Fin n → Mat 𝕋 (n + m) (n + m) :=
  let T : Array (Array (Array 𝕋)) := Array.ofFn fun i : Fin n =>
    Array.ofFn fun a : Fin (n + m) => Array.ofFn fun b : Fin (n + m) =>
      ((fm.hess (Interval.point xs) (Interval.point us) i).centerMat a b)
  fun i a b => ((T.getD i.val #[]).getD a.val #[]).getD b.val zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
