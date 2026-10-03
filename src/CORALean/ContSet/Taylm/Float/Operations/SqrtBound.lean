import CORALean.Global.SqrtDeriv
import CORALean.Global.Float.HalfPow
import CORALean.Global.Float.IntRound
import CORALean.Global.Float.Sqrt
import CORALean.Global.Float.PowUp

/-!
# A bound of the `(N+1)`-th derivative of `√`, rounded up

`|√⁽ᴺ⁺¹⁾ ξ| ≤ (|sqrtDeriv (N+1)| / 2ᴺ⁺¹) · √m₀ · (1/m₀)ᴺ⁺¹` for `ξ ≥ m₀ > 0`: the integer by
`intUp` and exact halvings, `√m₀` by `sqrtUp`, `(1/m₀)ᴺ⁺¹` by `powUp` of `divUp one m₀`, the
product rounded up. `q` is the precision of the square root.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sqrtBound (q : ℕ) (m₀ : 𝕋) (N : ℕ) : 𝕋 :=
  mulUp (mulUp (halfPow (N + 1) (intUp |sqrtDeriv (N + 1)|)) (sqrtUp q m₀))
    (powUp (divUp one m₀) (N + 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
