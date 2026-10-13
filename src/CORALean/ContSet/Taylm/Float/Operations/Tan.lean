import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Interval.Float.Operations.EvalList
import CORALean.Global.OdeList
import CORALean.Global.Float.Tan
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.DivFact

/-!
# `Taylm.tan`

The exact layer's `tan` with every number enclosed. `tan' = 1 + tan²`, so the `k`-th
coefficient is `P(tan c) / k!` for the integer polynomial `P = odePoly (1 + X²) k`
(`odeL [1, 0, 1] k`): `tan c` is enclosed by `tanDown`/`tanUp`, `P` by `Interval.evalList`
on that enclosure, and the quotient by `k!` through the corner products with `[divFact (1, 1) k]`.
The Lagrange bound is the same polynomial of order `N+1` at `tan m`, `m` the magnitude of the
model, enclosed the same way, times `Bᴺ⁺¹ / (N+1)!`, each factor rounded up. `p` is the
precision of the sine and cosine (`Global/Float/SinCos`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.tan (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box, and `|ξ| ≤ m` on the hull of the centre and the box
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  let m := maximum (absolute c) (maximum (absolute b.1) (absolute b.2))
  -- `|tan⁽ᴺ⁺¹⁾| ≤ odePoly (1 + X²) (N+1)` at `tan m`
  let D := (Interval.evalList (tanDown p m) (tanUp p m) (odeL [1, 0, 1] (N + 1))).2
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2
  -- `tan c` between its roundings, and each `tan⁽ᵏ⁾ c` as the polynomial on that enclosure
  let t : 𝕋 × 𝕋 := (tanDown p c, tanUp p c)
  let deriv : ℕ → 𝕋 × 𝕋 := fun k => Interval.evalList t.1 t.2 (odeL [1, 0, 1] k)
  let invFact : ℕ → 𝕋 × 𝕋 := fun k => divFact (one, one) k
  T.compose c
    (fun k => Interval.mulLo (deriv k).1 (deriv k).2 (invFact k).1 (invFact k).2)
    (fun k => Interval.mulHi (deriv k).1 (deriv k).2 (invFact k).1 (invFact k).2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
