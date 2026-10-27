module

public import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float constant term encloses the dynamics at every parameter

For a float model enclosing the field and its Jacobians, the dynamics at the real value of the
float expansion point and at every parameter of the box lies in the enclosure `step_linearizeFFloat`
returns, whose center is the constant of the system `linearizeFloat` returns.

## Inputs
* `sys` – parametric system
* `fm` – float model
* `xs` – float state expansion point
* `us` – float input expansion point
* `P` – parameter box
* `p` – parameter vector

## Hypotheses
* `h` – the float model encloses the system
* `hp` – `p` lies in the box

## Conclusion
* the dynamics at the parameter lie in the float constant term enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The dynamics at every parameter of the box lie in the constant term's enclosure. -/
theorem NonlinParamSys.FloatModel.linearizeFloat_f_mem
    {sys : NonlinParamSys n m q} {fm : NonlinParamSys.FloatModel 𝕋 n m q}
    (h : fm.Encloses sys) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q))
    {p : Vec ℝ q} (hp : p ∈ construct P) :
    sys.f (toRealVec xs) (toRealVec us) p ∈
      construct (fm.step_linearizeFFloat xs us P) :=
  h.f_mem _ _ _ _ (Interval.mem_point xs) _ (Interval.mem_point us) p hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
