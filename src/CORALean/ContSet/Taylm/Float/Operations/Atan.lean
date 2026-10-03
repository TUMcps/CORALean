import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.MagUp
import CORALean.ContSet.Interval.Float.Operations.EvalList
import CORALean.Global.RecList
import CORALean.Global.Float.InverseTrig
import CORALean.Global.Float.PowDown

/-!
# `Taylm.atan`

The exact layer's `atan` with every number enclosed. `atan⁽ʲ⁺¹⁾ x = atanPoly j x · w⁽ʲ⁺¹⁾` with
`w = (1 + x²)⁻¹`, so the `(j+1)`-th coefficient is `atanPoly j (c) · wʲ⁺¹ / (j+1)!`: the integer
polynomial (`recL [1, 0, 1] (j ↦ -2(j+1)) j`) by `Interval.evalList` on `[c, c]`, `wʲ⁺¹` between
`powDown` and `powUp` of the roundings of `w` (above by `1`, `w ≤ 1`), and `1 / (j+1)!` by
`divFact`, the three through the corner products; the zeroth is `atanDown`/`atanUp`. The Lagrange
bound is `atanDom N` (`recL [1, 0, 1] (j ↦ 2(j+1)) N`) at the magnitude `Taylm.magUp`, enclosed by
`Interval.evalList` (`w ≤ 1` drops the power). `p` and `q` are the precisions of
`Global/Float/InverseTrig`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.atan (p q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let m := T.magUp
  -- `|atan⁽ᴺ⁺¹⁾| ≤ atanDom N` at `m`
  let D := (Interval.evalList m m (recL [1, 0, 1] (fun j => 2 * ((j : ℤ) + 1)) N)).2
  -- `w = (1 + c²)⁻¹` between its roundings
  let wl := maximum zero (divDown one (addUp one (mulUp c c)))
  let wh := divUp one (maximum one (addDown one (mulDown c c)))
  let coef : ℕ → 𝕋 × 𝕋 := fun k =>
    match k with
    | 0 => (atanDown p q c, atanUp p q c)
    | j + 1 =>
      let P := Interval.evalList c c (recL [1, 0, 1] (fun j => -(2 * ((j : ℤ) + 1))) j)
      let G := divFact (one, one) (j + 1)
      let W : 𝕋 × 𝕋 := (Interval.mulLo (powDown wl (j + 1)) (powUp wh (j + 1)) G.1 G.2,
        Interval.mulHi (powDown wl (j + 1)) (powUp wh (j + 1)) G.1 G.2)
      (Interval.mulLo P.1 P.2 W.1 W.2, Interval.mulHi P.1 P.2 W.1 W.2)
  T.taylor c (fun k => (coef k).1) (fun k => (coef k).2) D

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
