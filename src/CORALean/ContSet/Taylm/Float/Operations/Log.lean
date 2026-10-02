import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Operations.LogCoef

/-!
# `Taylm.log`

The exact layer's `log` with every number enclosed: the coefficients by `logCoef`, and the
Lagrange bound `N!/Lᴺ⁺¹ · Bᴺ⁺¹/(N+1)!`, which is `(B/L)ᴺ⁺¹/(N+1)`, rounded up, `L` the
bottom of the hull and `B` the reach. `q` and `s` are `logUp`'s precision and steps.
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

def Taylm.log (q s : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B`, and the remainder `(B / L)ᴺ⁺¹ / (N+1)` at the bottom `L` of the hull
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))
  let ρ := divUp (powUp (divUp B (minimum c b.1)) (N + 1)) (maximum one (nsmulDown (N + 1) one))
  T.compose c (fun k => (Taylm.logCoef q s c k).1) (fun k => (Taylm.logCoef q s c k).2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
