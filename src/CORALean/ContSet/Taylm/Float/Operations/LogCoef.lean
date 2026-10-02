import CORALean.ContSet.Taylm.Float.Taylm
import CORALean.Global.Float.Log
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.PowDown

/-!
# The coefficients of `log`, enclosed

`log c` from `logUp` above and, through `log c = -log (1/c)`, from `logUp` of `1/c` rounded
up below, which needs no `1 ≤ c` as `logDown` would. The rest are `(-1)ᵏ⁺¹ / (k cᵏ)`: a
power of `1/c` each way, divided by `k` each way, the ends swapped where the sign is negative.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An enclosure of the `k`-th coefficient of `log` at `c`: `log c` at `k = 0`, else
`(-1)^(k+1) / (k cᵏ)`. `q` is the precision of `logUp`'s exponential and `s` its steps. -/
def Taylm.logCoef (q s : ℕ) (c : 𝕋) : ℕ → 𝕋 × 𝕋
  | 0 => (neg (logUp q s (divUp one c)), logUp q s c)
  | k + 1 =>
    let lo := divDown (powDown (maximum zero (divDown one c)) (k + 1)) (nsmulUp (k + 1) one)
    let hi := divUp (powUp (divUp one c) (k + 1)) (maximum one (nsmulDown (k + 1) one))
    if k % 2 = 0 then (lo, hi) else (neg hi, neg lo)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
