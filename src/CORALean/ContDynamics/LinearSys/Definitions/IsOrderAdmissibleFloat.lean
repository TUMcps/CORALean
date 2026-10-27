module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# A Taylor order the float enclosures of `e^{At}` admit over a time range

The float remainder `MatExp.expRemainderBound` is sound once `nrm / (η + 2) ≤ 1/2`, `nrm` a float
bound on `‖t A‖` over every `t ∈ [tLo, tHi]` — here the one `MatExp.normUpperBound` reads off the
interval matrix `[tLo, tHi] · A`. The geometric series of the remainder bound needs
`nrm / (η + 2) < 1`, the condition [1, Thm. 1] states; the float layer asks `≤ 1/2`, its geometric
factor being the fixed constant `2`, where the exact layer's `timeInterval_outer` asks `< 1`. At
least `2`, from no paper: as `MatExp.intervalCorrectionMatrix`'s guarantee needs.

## Inputs
* `sys` – linear system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order

## Output
* proposition that the order is at least two and its float remainder bound is sound

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `η` is at least `2` and the float remainder bound at `[tLo, tHi] · A` is
sound at it. -/
def LinearSys.IsOrderAdmissibleFloat (sys : LinearSys 𝕋 n) (tLo tHi : 𝕋) (η : ℕ) : Prop :=
  2 ≤ η ∧ toReal (MatExp.normUpperBound (Interval.smul tLo tHi (Interval.point sys.A)))
    / ((η : ℝ) + 2) ≤ 1 / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
