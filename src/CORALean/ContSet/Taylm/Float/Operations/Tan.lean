module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.EvalList
public import CORALean.Global.OdeList
public import CORALean.Global.Float.Tan
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

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
-- Last update:   14-October-2026
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
  let B := maximum zero (maximum (subUp b.sup c) (subUp c b.inf))
  let m := maximum (absolute c) (maximum (absolute b.inf) (absolute b.sup))
  -- `|tan⁽ᴺ⁺¹⁾| ≤ odePoly (1 + X²) (N+1)` at `tan m`
  let D := (Interval.evalList (tanDown p m) (tanUp p m) (odeL [1, 0, 1] (N + 1))).sup
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2
  -- `tan c` between its roundings, and each `tan⁽ᵏ⁾ c` as the polynomial on that enclosure
  let t : Interval 𝕋 := ⟨tanDown p c, tanUp p c⟩
  let deriv : ℕ → Interval 𝕋 := fun k => Interval.evalList t.inf t.sup (odeL [1, 0, 1] k)
  let invFact : ℕ → Interval 𝕋 := fun k => ⟨(divFact (one, one) k).1, (divFact (one, one) k).2⟩
  T.compose c
    (fun k => Interval.mulLo (deriv k).inf (deriv k).sup (invFact k).inf (invFact k).sup)
    (fun k => Interval.mulHi (deriv k).inf (deriv k).sup (invFact k).inf (invFact k).sup) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
