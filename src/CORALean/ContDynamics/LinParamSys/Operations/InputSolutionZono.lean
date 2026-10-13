import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinParamSys.Operations.InputTermZono
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval

/-!
# The set every input contributes over one step, at a matrix zonotope

[1, Prop. 3.6]: `LinearSys.inputSolution` adapted to a system matrix that is a
matrix zonotope `A_Z`. Orders `0` and `1` — "linear" and "quadratic" — are
`inputTermZono`, computed exactly through the matrix zonotope; from order `2`
on, `A_Z` is over-approximated by its enclosing interval matrix `A_Z.interval`,
matching `inputTaylorSumTail` and `intervalInputRemainder` from there.

[1] remarks that this may not be factored into `(r + A_Zr²/2!)U`: the four
pieces below stay four separate products, each its own `mtimes`, exactly as
printed.

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
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Everything the input can contribute over one step, at every matrix the
system's matrix zonotope holds: the linear and quadratic orders exact, every
order past them and the remainder over the enclosing interval matrix. -/
noncomputable def LinParamSys.inputSolutionZono (sys : LinParamSys 𝕄𝒵 n) (r : ℝ) (η : ℕ)
    (U : S n) : S n :=
  Mtimes.mtimes (𝕄 := 𝕄𝒵) (sys.inputTermZono r 0) U ⊞
    Mtimes.mtimes (𝕄 := 𝕄𝒵) (sys.inputTermZono r 1) U ⊞
    (LinParamSys.mk (𝕄 := ℐ) sys.A.interval).inputTaylorSumTail r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder sys.A.interval r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
