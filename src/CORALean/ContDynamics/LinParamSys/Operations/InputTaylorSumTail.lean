module

public import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# Orders `2` through `η` of the input solution, over an interval matrix, summed

The part of [1, Thm. 1] that [1, Sec. 4.4] over-approximates by interval matrices:
`LinParamSys.inputTaylorSum` starting
at order `2` rather than `0`, since orders `0` and `1` are the exact part
`step_inputTermZono` supplies instead. Below order `2` the sum is empty, matched by
`Interval.point 0`, whose singleton `{0}` is what an empty sum denotes.

Recursive rather than a fold over `Finset`, for the reason `inputTaylorSum`
gives: `plus` is only an enclosure and never has to be reassociated.

## Inputs
* `sys` – system
* `r` – step size
* `U` – input set

## Output
* orders 2 up to a given order of the input solution, summed

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Orders `2 … η` of the input solution, `0` below order `2`. -/
noncomputable def LinParamSys.inputTaylorSumTail (sys : LinParamSys ℐ n) (r : ℝ) (U : S n) :
    ℕ → S n
  | 0 => Mtimes.mtimes (𝕄 := ℐ) (Interval.point 0) U
  | 1 => Mtimes.mtimes (𝕄 := ℐ) (Interval.point 0) U
  | 2 => Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r 2) U
  | k + 3 => Plus.plus (sys.inputTaylorSumTail r U (k + 2))
      (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r (k + 3)) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
