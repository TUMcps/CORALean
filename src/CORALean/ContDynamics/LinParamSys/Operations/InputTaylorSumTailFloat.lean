module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# Orders `2` through `η` of the input solution, in floats

`LinParamSys.inputTaylorSumTail` computed in `𝕋` [1, Prop. 3.6]: `inputTaylorSumFloat`
starting at order `2`, orders `0` and `1` being `inputTermZonoFloat`'s. Below order `2`
the sum is empty, matched by the zero point interval, as the exact layer matches it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
def LinParamSys.inputTaylorSumTailFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (r : 𝕋) (V : Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (Interval.point fun _ _ => zero) V
  | 1 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (Interval.point fun _ _ => zero) V
  | 2 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalInputTerm sys.A r 2) V
  | k + 3 => sys.inputTaylorSumTailFloat r V (k + 2) ⊞
      Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalInputTerm sys.A r (k + 3)) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
