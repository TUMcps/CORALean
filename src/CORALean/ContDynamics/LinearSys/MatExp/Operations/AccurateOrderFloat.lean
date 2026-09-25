import CORALean.ContDynamics.LinearSys.MatExp.Operations.AccurateOrderFromFloat

/-!
# `MatExp.accurateOrder`, a Taylor order admissible and accurate to a tolerance

`admissibleOrder` with a second test: the first `η` from `η₀` on at which the
float remainder bound is sound (`nrm ≤ (η + 2)/2`) *and* `expRemainderBound nrm η`
is at most `tol`. Admissibility alone lets the remainder grow like
`nrm^{η+1}/(η+1)!` at `η ≈ 2 nrm`, which is useless once `nrm` is large; the
tolerance is what keeps an enclosure at a long time as tight as one at a short.

`accurateOrderFrom` is the loop, started here at `η₀` with the power, the
factorial and the count it carries; each candidate then costs a constant.
`none` after `fuel` orders, rather than an unchecked one.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `η ∈ [η₀, η₀ + fuel)` with `nrm ≤ (η + 2)/2` and
`expRemainderBound nrm η ≤ tol`, both certified by `le`. -/
def MatExp.accurateOrder (nrm tol : 𝕋) (η₀ fuel : ℕ) : Option ℕ :=
  MatExp.accurateOrderFrom nrm tol fuel η₀ (MatExp.powUp (η₀ + 1) nrm)
    (MatExp.factorialDown (η₀ + 1)) (nsmulDown (η₀ + 2) one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
