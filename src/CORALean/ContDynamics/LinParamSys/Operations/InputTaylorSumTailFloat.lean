module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# Orders `2` through `η` of the input solution, in floats

`LinParamSys.inputTaylorSumTail` computed in `𝕋` ([1, Thm. 1], [1, Sec. 4.4]): `inputTaylorSumFloat`
starting at order `2`, orders `0` and `1` being `inputTermZonoFloat`'s. Below order `2`
the sum is empty, matched by the zero point interval, as the exact layer matches it.

## Inputs
* `sys` – system
* `r` – step size
* `V` – input zonotope

## Output
* orders 2 up to a given order of the input solution, summed

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⊕_{2 ≤ i ≤ η} [Aⁱ r^{i+1}/(i+1)!] V` over the float box `sys.A`, `0 · V` below order `2`. -/
def LinParamSys.inputTaylorSumTailFloat (sys : LinParamSys ℐ[𝕋] n)
    (r : 𝕋) (V : Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (Interval.point fun _ _ => zero) V
  | 1 => Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (Interval.point fun _ _ => zero) V
  | 2 => Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (MatExp.intervalInputTerm sys.A r 2) V
  | k + 3 => sys.inputTaylorSumTailFloat r V (k + 2) ⊞
      Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm sys.A r (k + 3)) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
