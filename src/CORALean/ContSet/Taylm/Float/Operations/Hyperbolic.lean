import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.Global.Float.Hyperbolic
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.DivFact

/-!
# `Taylm.hyperbolic`: the Taylor model of `sinh` and of `cosh`

The derivatives of `sinh` and `cosh` alternate between the two, so the `k`-th coefficient at the
centre `c` is `sinh c / k!` or `cosh c / k!` by the parity of `k`: `first` says whether the even
coefficients are `sinh`'s (`Taylm.sinh`) or `cosh`'s (`Taylm.cosh`). `sinh c` and `cosh c` are
enclosed by `sinhDown`/`sinhUp` and `coshDown`/`coshUp`, and the quotient by `k!` as the product
with `[divFact (1, 1) k]` through the four corner products `mulLo`, `mulHi`, since `sinh c` has no
sign. The remainder is Lagrange's: `cosh` at the magnitude `m` of the model bounds every
derivative, times `Bᴺ⁺¹ / (N+1)!` with `B` the reach, each factor rounded up. `p` is the precision
of the exponentials (`Global/Float/Exp`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.hyperbolic (p : ℕ) (first : Bool) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box, and `|ξ| ≤ m` on the hull of the centre and the box
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  let m := maximum (absolute c) (maximum (absolute b.1) (absolute b.2))
  let D := coshUp p m
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2
  -- the `k`-th derivative at `c` is `sinh c` or `cosh c` by parity, over `k!`
  let base : ℕ → 𝕋 × 𝕋 := fun k =>
    if (k % 2 == 0) == first then (sinhDown p c, sinhUp p c) else (coshDown p c, coshUp p c)
  let invFact : ℕ → 𝕋 × 𝕋 := fun k => divFact (one, one) k
  T.compose c
    (fun k => Interval.mulLo (base k).1 (base k).2 (invFact k).1 (invFact k).2)
    (fun k => Interval.mulHi (base k).1 (base k).2 (invFact k).1 (invFact k).2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
