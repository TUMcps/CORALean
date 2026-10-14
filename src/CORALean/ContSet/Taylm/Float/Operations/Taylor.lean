module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.taylor`

The expansion of an elementary function at the constant part, every number enclosed: the
coefficients are given as enclosures `lo k`, `hi k` of `g⁽ᵏ⁾(c) / k!`, and the Lagrange remainder
is a rounded-up bound `D` of `|g⁽ᴺ⁺¹⁾|` times `Bᴺ⁺¹ / (N+1)!`, `B` the reach of the model from
`c`, each factor rounded up. What is left for each function is its derivatives.
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

def Taylm.taylor (T : Taylm 𝕋 n) (c : 𝕋) (lo hi : ℕ → 𝕋) (D : 𝕋) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let b := T.bounds
  -- `|f t - c| ≤ B` on the box
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  T.compose c lo hi N (mulUp (mulUp D (powUp B (N + 1))) (divFact (one, one) (N + 1)).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
