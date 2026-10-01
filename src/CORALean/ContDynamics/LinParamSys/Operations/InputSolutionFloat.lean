import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat

/-!
# What the input contributes over one step at every member, in floats

`LinParamSys.inputSolution` computed in `𝕋`: the Taylor orders up to `η`, and the
remainder `[E(r)·r]` over the whole box `sys.A`, `MatExp.intervalInputRemainder`
at `sys.A` itself, times the input set.

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

/-- [1, Thm. 3.1] in floats over every `A ∈ sys.A`: `⊕ᵢ [Aⁱr^{i+1}/(i+1)!] V ⊕ [E(r)·r] V`. -/
def LinParamSys.inputSolutionFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (r : 𝕋) (η : ℕ) (V : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  sys.inputTaylorSumFloat r V η ⊞ Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (MatExp.intervalInputRemainder sys.A r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
