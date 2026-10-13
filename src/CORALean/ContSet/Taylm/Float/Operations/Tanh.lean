module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
public import CORALean.ContSet.Taylm.Float.Operations.Bounds
public import CORALean.ContSet.Interval.Float.Operations.EvalList
public import CORALean.Global.OdeList
public import CORALean.Global.Float.Hyperbolic
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.tanh`

The exact layer's `tanh` with every number enclosed. `tanh' = 1 - tanh²`, so the `k`-th
coefficient is `P(tanh c) / k!` for the integer polynomial `P = odePoly (1 - X²) k`
(`odeL [1, 0, -1] k`): `tanh c` is enclosed by `tanhDown`/`tanhUp`, `P` by `Interval.evalList`
on that enclosure, and the quotient by `k!` through the corner products with `[divFact (1, 1) k]`.
The Lagrange bound is `odePoly (1 + X²) (N+1)` at one (`odeL [1, 0, 1] (N+1)` on `[1, 1]`) times
`Bᴺ⁺¹ / (N+1)!`, each factor rounded up. `p` is the precision of the exponentials
(`Global/Float/Exp`).
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

def Taylm.tanh (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  -- `|tanh⁽ᴺ⁺¹⁾| ≤ odePoly (1 + X²) (N+1)` at one
  let D := (Interval.evalList one one (odeL [1, 0, 1] (N + 1))).2
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2
  -- `tanh c` between its roundings, and each `tanh⁽ᵏ⁾ c` as the polynomial on that enclosure
  let t : 𝕋 × 𝕋 := (tanhDown p c, tanhUp p c)
  let deriv : ℕ → 𝕋 × 𝕋 := fun k => Interval.evalList t.1 t.2 (odeL [1, 0, -1] k)
  let invFact : ℕ → 𝕋 × 𝕋 := fun k => divFact (one, one) k
  T.compose c
    (fun k => Interval.mulLo (deriv k).1 (deriv k).2 (invFact k).1 (invFact k).2)
    (fun k => Interval.mulHi (deriv k).1 (deriv k).2 (invFact k).1 (invFact k).2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
