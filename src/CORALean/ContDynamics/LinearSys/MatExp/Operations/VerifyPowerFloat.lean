module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.verifyPowerFloat`, the scaled powers `Aⁱ/i!` of CORA's `aux_getApower`

CORA's `priv_verifyRA_supportFunc` keeps `Apower{i} = Apower{i-1} * A / i`, the powers of `A`
divided by `i!`, for its Taylor sums. Here the same recursion over boxes: the product with the
point `A` is `Interval.matMul` (each entry a sum over the inner index nested to the right, that
is, accumulated from the last index down), and the division by `i` takes `i` between
`max 1 (nsmulDown i 1)` and `nsmulUp i 1`, which at `nearest` are both `i`. So at `nearest` both
bounds are the one product CORA.cpp forms, `X A / i`.

## Inputs
* `A` – float system matrix

## Output
* float box enclosing `Aⁱ/i!`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The box divided by `k ≥ 1`: the corners at `k` from below and from above. -/
@[step_of MatExp.verifyPowerFloat]
def MatExp.step_verifyDivNatFloat (P : Interval (Mat 𝕋 n n)) (k : ℕ) : Interval (Mat 𝕋 n n) :=
  let dLo := maximum one (nsmulDown k one)                               -- ≤ k, ≥ 1
  let dHi := nsmulUp k one                                               -- ≥ k
  ⟨fun j l => minimum (divDown (P.inf j l) dLo) (divDown (P.inf j l) dHi),
    fun j l => maximum (divUp (P.sup j l) dLo) (divUp (P.sup j l) dHi)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Apower{i} = Apower{i-1} * A / i` over boxes, from the identity. -/
def MatExp.verifyPowerFloat (A : Mat 𝕋 n n) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.point (diagonalBlock fun _ => one)                     -- A⁰/0! = I
  | i + 1 =>
    let X := Interval.matMul (MatExp.verifyPowerFloat A i) (Interval.point A)  -- Apower{i} * A
    (MatExp.step_verifyDivNatFloat X (i + 1)).materialiseMat                   -- / (i + 1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
