module

public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTermBoxFloat
public import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# How far `inputTaylorSumFloat` reaches beyond the exact Taylor sum

The float sum `⊕_{i ≤ η} [Tᵢ] U` against the exact `⊕_{i ≤ η} Tᵢ U` at `U`'s
nominal zonotope: every order pays `inputTermBoxFloat`, and every float `⊞`
its `plusBox`. A summand of `inputSolutionBoxFloat`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `U` – float input zonotope

## Output
* float zonotope of how far the float Taylor sum reaches beyond the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
    let T := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm (Interval.point sys.A) r (i + 1)) U   -- [T_{i+1}] U
    (sys.inputTaylorSumBoxFloat r U i ⊞ sys.inputTermBoxFloat r U (i + 1)) ⊞
      (Zonotope.plusBox S T).zonotope                               -- S ⊞ T beyond S + T

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
