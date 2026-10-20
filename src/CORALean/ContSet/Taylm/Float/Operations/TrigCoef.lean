module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.SinCos
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Taylm.trigCoef`

Enclosures of the `k`-th Taylor coefficients of `sin` and of `cos` at `c`,
`sin⁽ᵏ⁾(c) / k!` and `cos⁽ᵏ⁾(c) / k!`, together: at `k = 0` the sine and cosine enclosures of
`Global/Float/SinCos`, and from `k` to `k + 1` the rule `sin' = cos`, `cos' = -sin`, divided by
`k + 1` between its two roundings. `p` is the number of halvings of the sine and cosine.

## Inputs
* `p` – precision of the halvings
* `c` – center

## Output
* enclosures of the sine and cosine Taylor coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.trigCoef (p : ℕ) (c : 𝕋) : ℕ → Interval 𝕋 × Interval 𝕋
  | 0 => (⟨sinDown p c, sinUp p c⟩, ⟨cosDown p c, cosUp p c⟩)
  | k + 1 =>
    let d := Taylm.trigCoef p c k
    let mU := nsmulUp (k + 1) one                                   -- k + 1 from above
    let mD := maximum one (nsmulDown (k + 1) one)                   -- k + 1 from below, ≥ 1
    -- sin⁽ᵏ⁺¹⁾ = cos⁽ᵏ⁾ and cos⁽ᵏ⁺¹⁾ = -sin⁽ᵏ⁾, each over k + 1
    (⟨minimum (divDown d.2.inf mU) (divDown d.2.inf mD), maximum (divUp d.2.sup mU) (divUp d.2.sup
        mD)⟩,
      ⟨minimum (divDown (neg d.1.sup) mU) (divDown (neg d.1.sup) mD),
        maximum (divUp (neg d.1.inf) mU) (divUp (neg d.1.inf) mD)⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
