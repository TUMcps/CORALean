module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.Hyperbolic
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.hyperbolic`: the Taylor model of `sinh` and of `cosh`

The derivatives of `sinh` and `cosh` alternate between the two, so the `k`-th coefficient at the
center `c` is `sinh c / k!` or `cosh c / k!` by the parity of `k`: `first` says whether the even
coefficients are `sinh`'s (`Taylm.sinh`) or `cosh`'s (`Taylm.cosh`). `sinh c` and `cosh c` are
enclosed by `sinhDown`/`sinhUp` and `coshDown`/`coshUp`, and the quotient by `k!` as the product
with `[divFact ⟨1, 1⟩ k]` through the four corner products `mulLo`, `mulHi`, since `sinh c` has no
sign. The remainder is Lagrange's: `cosh` at the magnitude `m` of the model bounds every
derivative, times `Bᴺ⁺¹ / (N+1)!` with `B` the reach, each factor rounded up. `p` is the precision
of the exponentials (`Global/Float/Exp`).

## Inputs
* `p` – precision of the halvings
* `first` – flag for sinh instead of cosh
* `T` – Taylor model

## Output
* Taylor model of sinh or cosh of the argument
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
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
  -- `|f t - c| ≤ B` on the box, and `|ξ| ≤ m` on the hull of the center and the box
  let B := maximum zero (maximum (subUp b.sup c) (subUp c b.inf))
  let m := maximum (absolute c) (maximum (absolute b.inf) (absolute b.sup))
  let D := coshUp p m
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact ⟨one, one⟩ (N + 1)).sup
  -- the `k`-th derivative at `c` is `sinh c` or `cosh c` by parity, over `k!`
  let base : ℕ → Interval 𝕋 := fun k =>
    if (k % 2 == 0) == first then ⟨sinhDown p c, sinhUp p c⟩ else ⟨coshDown p c, coshUp p c⟩
  let invFact : ℕ → Interval 𝕋 := divFact ⟨one, one⟩
  T.compose c
    (fun k => Interval.mulLo (base k).inf (base k).sup (invFact k).inf (invFact k).sup)
    (fun k => Interval.mulHi (base k).inf (base k).sup (invFact k).inf (invFact k).sup) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
