import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat

/-!
# The set every input contributes over one step, in floats

`inputSolution` [1, Thm. 3.1] computed in `𝕋`: the orders up to `η` by
`inputTaylorSumFloat`, and everything past `η` in
`MatExp.intervalInputRemainder`, the float `E(r)·r` taken at the bound
`normUpperBound (r • A)` the exponential and the correction of the same step are
taken at — so the order `reachOrderFloat` admits for those admits this too.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 3.1] in floats: `⊕ᵢ [Aⁱr^{i+1}/(i+1)!] V ⊕ [E(r)·r] V`. -/
def LinearSys.inputSolutionFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) (V : Zonotope 𝕋 n) :
    Zonotope 𝕋 n :=
  sys.inputTaylorSumFloat r V η ⊞ Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
