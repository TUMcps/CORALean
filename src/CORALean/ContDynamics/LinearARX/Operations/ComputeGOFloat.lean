module

public import CORALean.ContDynamics.LinearARX.Definitions.GOFloat
public import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearARX.computeGOFloat`

CORA's `linearARX/computeGO` [1] with the output parameters as interval matrices over `𝕋`: the
powers of the converted system's `A` by `Interval.matPow`, each product with the stored output
and input matrices by `Interval.matMul`, the sums over steps and lags by `step_sumRangeFloat`, every
entry rounded outward. Soundness is `computeGOFloat_outer`.

## Inputs
* `sys` – ARX system
* `nk` – number of steps

## Output
* the output parameters as enclosing interval matrices

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- `∑ t < k, f t`, left to right. -/
@[step_of LinearARX.computeGOFloat]
def LinearARX.step_sumRangeFloat (f : ℕ → Interval (Mat 𝕋 m n)) : ℕ → Interval (Mat 𝕋 m n)
  | 0 => Interval.point fun _ _ => zero
  | k + 1 => Interval.matPlus (LinearARX.step_sumRangeFloat f k) (f k)

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output parameters for `nk` steps, as interval matrices enclosing `computeGO`'s. -/
def LinearARX.computeGOFloat (sys : LinearARX 𝕋 dy du p) (nk : ℕ) :
    LinearARX.GOFloat 𝕋 dy du p nk where
  C k := Interval.matMul (Interval.point sys.outputEq.C)
    ((Interval.point sys.toLinearSysDT.A).matPow k.val)
  D k i := LinearARX.step_sumRangeFloat (fun t =>
    LinearARX.step_sumRangeFloat (fun j =>
      if hj : j < p + 1 then
        if t + p - j = i.val then
          Interval.matMul (Interval.matMul (Interval.point sys.outputEq.C)
            ((Interval.point sys.toLinearSysDT.A).matPow (k.val - 1 - t)))
            (Interval.point (sys.inputMat ⟨j, hj⟩))
        else Interval.point fun _ _ => zero
      else Interval.point fun _ _ => zero) (p + 1)) k.val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
