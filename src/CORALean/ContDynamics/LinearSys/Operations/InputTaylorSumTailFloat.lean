module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# Orders `1` through `η` of the input solution, summed, in floats

`inputTaylorSumTail` computed in `𝕋`: [1, Alg. 2] line 16's `⊕_{i=1}^{η} ÃᵢU₀`, each order the
float box `intervalInputTerm` times `U`, summed by `⊞` in the same recursion; below order `1`
the point `0` matrix, as the exact one has the zero matrix.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Orders `1 … η` of the float input solution, `[0] U` below order `1`. -/
def LinearSys.inputTaylorSumTailFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (U : Zonotope (Vec 𝕋 n)) :
    ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (Interval.point fun _ _ => zero) U
  | 1 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm (Interval.point sys.A) r 1) U
  | i + 2 => sys.inputTaylorSumTailFloat r U (i + 1) ⊞
      Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalInputTerm (Interval.point sys.A) r (i + 2)) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
