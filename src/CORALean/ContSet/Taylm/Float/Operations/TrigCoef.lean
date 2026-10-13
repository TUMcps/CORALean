module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.SinCos

@[expose] public section

/-!
# `Taylm.trigCoef`

Enclosures of the `k`-th Taylor coefficients of `sin` and of `cos` at `c`,
`sin⁽ᵏ⁾(c) / k!` and `cos⁽ᵏ⁾(c) / k!`, together: at `k = 0` the sine and cosine enclosures of
`Global/Float/SinCos`, and from `k` to `k + 1` the rule `sin' = cos`, `cos' = -sin`, divided by
`k + 1` between its two roundings. `p` is the number of halvings of the sine and cosine.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.trigCoef (p : ℕ) (c : 𝕋) : ℕ → (𝕋 × 𝕋) × (𝕋 × 𝕋)
  | 0 => ((sinDown p c, sinUp p c), (cosDown p c, cosUp p c))
  | k + 1 =>
    let d := Taylm.trigCoef p c k
    let mU := nsmulUp (k + 1) one                                   -- k + 1 from above
    let mD := maximum one (nsmulDown (k + 1) one)                   -- k + 1 from below, ≥ 1
    -- sin⁽ᵏ⁺¹⁾ = cos⁽ᵏ⁾ and cos⁽ᵏ⁺¹⁾ = -sin⁽ᵏ⁾, each over k + 1
    ((minimum (divDown d.2.1 mU) (divDown d.2.1 mD), maximum (divUp d.2.2 mU) (divUp d.2.2 mD)),
      (minimum (divDown (neg d.1.2) mU) (divDown (neg d.1.2) mD),
        maximum (divUp (neg d.1.1) mU) (divUp (neg d.1.1) mD)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
