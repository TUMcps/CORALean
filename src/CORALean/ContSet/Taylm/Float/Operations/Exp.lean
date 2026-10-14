module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.exp`

The exact layer's `exp` with every number enclosed: the coefficients `exp c / k!` by
`divFact` from `expDown`/`expUp` at the centre, the reach `B` rounded up, and the Lagrange
bound `exp(max(c, hi)) Bᴺ⁺¹ / (N+1)!` as a product of upward roundings. `p` is the precision
of the two exponentials (`Global/Float/Exp`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.exp (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box, and `exp` at the top of the hull bounds every derivative
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  let D := expUp p (maximum c b.2)
  let ρ := mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2
  T.compose c (fun k => (divFact (expDown p c, expUp p c) k).1)
    (fun k => (divFact (expDown p c, expUp p c) k).2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
