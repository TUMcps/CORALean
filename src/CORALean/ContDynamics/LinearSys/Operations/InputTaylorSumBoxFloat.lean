import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat
import CORALean.ContDynamics.LinearSys.Operations.InputTermBoxFloat
import CORALean.ContSet.Zonotope.Float.Operations.PlusBox

/-!
# How far `inputTaylorSumFloat` reaches beyond the exact Taylor sum

The float sum `⊕_{i ≤ η} [Tᵢ] U` against the exact `⊕_{i ≤ η} Tᵢ U` at `U`'s
nominal zonotope: every order pays `inputTermBoxFloat`, and every float `⊞`
its `plusBox`. A summand of `inputSolutionBoxFloat`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `inputTaylorSumFloat r U i` holds beyond the exact sum at `U`'s nominal zonotope:
every order's box, and every float sum's `plusBox`. -/
def LinearSys.inputTaylorSumBoxFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (U : Zonotope (Vec 𝕋 n)) :
    ℕ → Zonotope (Vec 𝕋 n)
  | 0 => sys.inputTermBoxFloat r U 0
  | i + 1 =>
    let S := sys.inputTaylorSumFloat r U i                          -- the float sum so far
    let T := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm (Interval.point sys.A) r (i + 1)) U   -- [T_{i+1}] U
    (sys.inputTaylorSumBoxFloat r U i ⊞ sys.inputTermBoxFloat r U (i + 1)) ⊞
      (Zonotope.plusBox S T).zonotope                               -- S ⊞ T beyond S + T

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
