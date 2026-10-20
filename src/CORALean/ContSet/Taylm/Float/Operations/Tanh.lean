module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.EvalPolyCoeffs
public import CORALean.Global.OdeList
public import CORALean.Global.Float.Hyperbolic
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.tanh`

The exact layer's `tanh` with every number enclosed. `tanh' = 1 - tanh²`, so the `k`-th
coefficient is `P(tanh c) / k!` for the integer polynomial `P = odePoly (1 - X²) k`
(`odeL [1, 0, -1] k`): `tanh c` is enclosed by `tanhDown`/`tanhUp`, `P` by `Interval.evalPolyCoeffs`
on that enclosure, and the quotient by `k!` through the corner products with `[divFact ⟨1, 1⟩ k]`.
The Lagrange bound is `odePoly (1 + X²) (N+1)` at one (`odeL [1, 0, 1] (N+1)` on `[1, 1]`) times
`Bᴺ⁺¹ / (N+1)!`, each factor rounded up. `p` is the precision of the exponentials
(`Global/Float/Exp`).

## Inputs
* `p` – precision of the exponential
* `T` – Taylor model

## Output
* Taylor model of hyperbolic tangent of the argument
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

def Taylm.tanh (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box
  let B := maximum zero (maximum (subUp b.sup c) (subUp c b.inf))
  -- `|tanh⁽ᴺ⁺¹⁾| ≤ odePoly (1 + X²) (N+1)` at one
  let D := (Interval.evalPolyCoeffs one one (odeL [1, 0, 1] (N + 1))).sup
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact ⟨one, one⟩ (N + 1)).sup
  -- `tanh c` between its roundings, and each `tanh⁽ᵏ⁾ c` as the polynomial on that enclosure
  let t : Interval 𝕋 := ⟨tanhDown p c, tanhUp p c⟩
  let deriv : ℕ → Interval 𝕋 := fun k => Interval.evalPolyCoeffs t.inf t.sup (odeL [1, 0, -1] k)
  let invFact : ℕ → Interval 𝕋 := divFact ⟨one, one⟩
  T.compose c
    (fun k => Interval.mulLo (deriv k).inf (deriv k).sup (invFact k).inf (invFact k).sup)
    (fun k => Interval.mulHi (deriv k).inf (deriv k).sup (invFact k).inf (invFact k).sup) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
