module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.Log
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.PowDown
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Taylm.log`

The exact layer's `log` with every number enclosed: the coefficients by `aux_logCoef`, and the
Lagrange bound `N!/Lᴺ⁺¹ · Bᴺ⁺¹/(N+1)!`, which is `(B/L)ᴺ⁺¹/(N+1)`, rounded up, `L` the
bottom of the hull and `B` the reach. `q` and `s` are `logUp`'s precision and steps.

## Inputs
* `q` – precision of the exponential
* `s` – number of steps
* `T` – Taylor model

## Output
* Taylor model of the logarithm of the argument
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An enclosure of the `k`-th coefficient of `log` at `c`: `log c` at `k = 0`, else
`(-1)^(k+1) / (k cᵏ)`. `q` is the precision of `logUp`'s exponential and `s` its steps. -/
def Taylm.aux_logCoef (q s : ℕ) (c : 𝕋) : ℕ → Interval 𝕋
  | 0 => ⟨neg (logUp q s (divUp one c)), logUp q s c⟩
  | k + 1 =>
    let lo := divDown (powDown (maximum zero (divDown one c)) (k + 1)) (nsmulUp (k + 1) one)
    let hi := divUp (powUp (divUp one c) (k + 1)) (maximum one (nsmulDown (k + 1) one))
    if k % 2 = 0 then ⟨lo, hi⟩ else ⟨neg hi, neg lo⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.log (q s : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  -- `|f t - c| ≤ B`, and the remainder `(B / L)ᴺ⁺¹ / (N+1)` at the bottom `L` of the hull
  let B := maximum zero (maximum (subUp b.sup c) (subUp c b.inf))
  let ρ := divUp (powUp (divUp B (minimum c b.inf)) (N + 1)) (maximum one (nsmulDown (N + 1) one))
  T.compose c (fun k => (Taylm.aux_logCoef q s c k).inf) (fun k => (Taylm.aux_logCoef q s c k).sup)
    N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
