import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `Σᵢ Ãᵢ` over a float box

`particularCoeffSum` computed in `𝕋`: `Σᵢ₌ᵢ₀^η Ãᵢ`, the single matrix the correlated summand
of eq. (25) in [1, Prop. 11] applies to `U0` once, as a float interval matrix holding it at
every member of `A`. Each `Ãᵢ` is `intervalInputTerm`, the sum one `matPlus` per order,
stored as it is built; an empty range is the point `0`.

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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σᵢ₌ᵢ₀^η [Aⁱ Δt^{i+1}/(i+1)!]`, by recursion on `η`. -/
def MatExp.particularCoeffSum (A : Interval (Mat 𝕋 n n)) (Δt : 𝕋) (i0 : ℕ) :
    ℕ → Interval (Mat 𝕋 n n)
  | 0 => if i0 = 0 then MatExp.intervalInputTerm A Δt 0                -- Ã₀
      else Interval.point fun _ _ => zero                              -- nothing
  | η + 1 => if i0 ≤ η + 1 then                                        -- … + Ã_{η+1}
        (Interval.matPlus (MatExp.particularCoeffSum A Δt i0 η)
          (MatExp.intervalInputTerm A Δt (η + 1))).materialiseMat
      else Interval.point fun _ _ => zero                              -- nothing

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
