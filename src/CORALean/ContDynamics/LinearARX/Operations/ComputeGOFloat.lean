import CORALean.ContDynamics.LinearARX.Definitions.GOFloat
import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
import CORALean.ContDynamics.LinearARX.Operations.SumRangeFloat
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatPow

/-!
# `LinearARX.computeGOFloat`

CORA's `linearARX/computeGO` [1] with the output parameters as interval matrices over `𝕋`: the
powers of the converted system's `A` by `Interval.matPow`, each product with the stored output
and input matrices by `Interval.matMul`, the sums over steps and lags by `sumRangeFloat`, every
entry rounded outward. Soundness is `computeGOFloat_outer`.

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output parameters for `nk` steps, as interval matrices enclosing `computeGO`'s. -/
def LinearARX.computeGOFloat (sys : LinearARX 𝕋 dy du p) (nk : ℕ) :
    LinearARX.GOFloat 𝕋 dy du p nk where
  C k := Interval.matMul (Interval.point sys.outputEq.C)
    ((Interval.point sys.toLinearSysDT.A).matPow k.val)
  D k i := LinearARX.sumRangeFloat (fun t =>
    LinearARX.sumRangeFloat (fun j =>
      if hj : j < p + 1 then
        if t + p - j = i.val then
          Interval.matMul (Interval.matMul (Interval.point sys.outputEq.C)
            ((Interval.point sys.toLinearSysDT.A).matPow (k.val - 1 - t)))
            (Interval.point (sys.inputMat ⟨j, hj⟩))
        else Interval.point fun _ _ => zero
      else Interval.point fun _ _ => zero) (p + 1)) k.val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
