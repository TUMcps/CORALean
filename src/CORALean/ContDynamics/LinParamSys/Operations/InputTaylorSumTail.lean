module

public import CORALean.ContDynamics.LinParamSys.Operations.InputTerm
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# Orders `2` through `η` of the input solution, over an interval matrix, summed

[1, Prop. 3.6]'s over-approximated part: `LinParamSys.inputTaylorSum` starting
at order `2` rather than `0`, since orders `0` and `1` are the exact part
`inputTermZono` supplies instead. Below order `2` the sum is empty, matched by
`Interval.point 0`, whose singleton `{0}` is what an empty sum denotes.

Recursive rather than a fold over `Finset`, for the reason `inputTaylorSum`
gives: `plus` is only an enclosure and never has to be reassociated.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
