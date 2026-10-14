module

public import CORALean.ContSet.Interval.Float.Operations.EvalList
public import CORALean.Global.RecList
public import CORALean.Global.Float.InvSqrtOneSub
public import CORALean.Global.Float.PowUp

@[expose] public section

/-!
# A bound of the `(N+1)`-th derivative of `arcsin` and `arccos`, rounded up

`|arcsin⁽ᴺ⁺¹⁾| = |arccos⁽ᴺ⁺¹⁾| ≤ asinDom N (m) · (√(1 - m²))⁻⁽²ᴺ⁺¹⁾` on `|x| ≤ m < 1`: the
integer polynomial `recL [1, 0, 1] (j ↦ 2j+1) N` by `Interval.evalList` on `[m, m]`, the power
of `invSqrtOneSubHi`, the product rounded up. `q` is the precision of the square root.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.arcsinBound (q : ℕ) (m : 𝕋) (N : ℕ) : 𝕋 :=
  mulUp (Interval.evalList m m (recL [1, 0, 1] (fun j => 2 * (j : ℤ) + 1) N)).sup
    (powUp (invSqrtOneSubHi q m) (2 * N + 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
