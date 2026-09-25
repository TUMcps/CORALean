import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat

/-!
# `MatExp.accurateOrderFrom`, the loop `accurateOrder` runs

From order `η` on, carrying `p = powUp (η + 1) nrm`, `f = factorialDown (η + 1)`
and `c = nsmulDown (η + 2) one` and advancing each by the step of its own
recursion, so a candidate costs a constant and what it compares is literally
`nrm ≤ half (η + 2)↓` and `expRemainderBound nrm η ≤ tol`. Given other values
it still only accepts what its tests certify; the pinned values are what make
those tests the ones named.
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

/-- The first order from `η` passing both tests, within `fuel` orders. -/
def MatExp.accurateOrderFrom (nrm tol : 𝕋) : ℕ → ℕ → 𝕋 → 𝕋 → 𝕋 → Option ℕ
  | 0, _, _, _, _ => none
  | fuel + 1, η, p, f, c =>
    if le nrm (half c) && le (mulUp (divUp p f) (addUp one one)) tol then some η
    else MatExp.accurateOrderFrom nrm tol fuel (η + 1) (mulUp nrm p)
      (maximum one (mulDown (maximum zero c) f)) (addDown one c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
