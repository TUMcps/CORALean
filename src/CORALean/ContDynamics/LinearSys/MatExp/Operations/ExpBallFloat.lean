module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.expBallFloat`, `e^{AΔt}` as a float matrix and a balanced radius

CORA's `priv_verifyRA_supportFunc` propagates its directions by a point `expm(A Δt)`, which
encloses nothing. Here the same scaling and squaring, with a radius: `D̃` and `r` such that
`‖S⁻¹(e^{AΔt} − D̃)S‖ ≤ r` for `S = diag s`. `σ` exact halvings bring the balanced norm `ν` of
`AΔt` to at most `4`; the Taylor series of `A h` is summed to the first order `K ≥ 6` whose
remainder is at most `2⁻⁸⁰` (`MatExp.expIntervalTaylor` over `[A h]`); each of the `σ` squarings
takes the upper end of `D̃ D̃` and the radius `(2‖D̃‖ + r) r` plus the box's width. At `nearest`
every box is a point, each squaring the one product CORA forms. One radius rather than an
interval matrix: the interval squaring of `LinearSys.expSquaringFloat` grows with `|D̃|`.

## Inputs
* `A` – float system matrix
* `s` – positive float scales
* `Δt` – float step length

## Output
* the float matrix `D̃` and the radius `r`, none if no halving count or order is found
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

/-- `max 0 (maxⱼ Σₖ |m_jk| s_k / s_j)`, every operation rounded up: `≥ ‖S⁻¹ M S‖`. -/
@[step_of MatExp.expBallFloat]
def MatExp.step_scaledNormUpFloat (s : Vec 𝕋 n) (M : Mat 𝕋 n n) : 𝕋 :=
  maximum zero (maximumOver fun j => sumUp fun k => divUp (mulUp (absolute (M j k)) (s k)) (s j))

/-- One squaring: the upper end of `D̃ D̃`, and the radius `(2p + r) r` plus the box's width,
`p` the balanced norm of `D̃`. -/
@[step_of MatExp.expBallFloat]
def MatExp.step_expBallSquareFloat (s : Vec 𝕋 n) (B : Mat 𝕋 n n × 𝕋) : Mat 𝕋 n n × 𝕋 :=
  let Q := (Interval.matMul (Interval.point B.1) (Interval.point B.1)).materialiseMat -- [D̃ D̃]
  let p := MatExp.step_scaledNormUpFloat s B.1                                  -- ≥ ‖S⁻¹ D̃ S‖
  let w := MatExp.step_scaledNormUpFloat s fun j k => subUp (Q.sup j k) (Q.inf j k)  -- the width
  (Q.sup, addUp (mulUp (addUp (addUp p p) B.2) B.2) w)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `D̃` and `r` with `‖S⁻¹(e^{AΔt} − D̃)S‖ ≤ r`: the Taylor series of `A Δt / 2^σ` to the first
order from `6` whose remainder is at most `2⁻⁸⁰`, squared `σ` times. Few halvings, many orders: an
order is a product with `A`, a squaring a dense product. -/
def MatExp.expBallFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋) : Option (Mat 𝕋 n n × 𝕋) := do
  let ν := mulUp (MatExp.step_scaledNormUpFloat s A) Δt                         -- ≥ ‖S⁻¹ AΔt S‖
  let σ ← (List.range 1100).find? fun σ => le (half^[σ] ν) (nsmulDown 4 one) -- ν / 2^σ ≤ 4
  let h := half^[σ] Δt                                                    -- Δt / 2^σ
  let νh := half^[σ] ν                                                    -- ≥ ‖S⁻¹ A h S‖
  let K ← (List.range' 6 55).find? fun K =>                               -- the order
    le (MatExp.expRemainderBound νh K) (half^[80] one)
  let T := MatExp.expIntervalTaylor (Interval.smul h h (Interval.point A)) K -- [Σ (Ah)ⁱ/i!]
  let w := MatExp.step_scaledNormUpFloat s fun j k => subUp (T.sup j k) (T.inf j k) -- its width
  let r₀ := addUp (MatExp.expRemainderBound νh K) w                       -- ≥ ‖S⁻¹(e^{Ah}−D̃₀)S‖
  pure ((MatExp.step_expBallSquareFloat s)^[σ] (T.sup, r₀))               -- squared σ times

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
