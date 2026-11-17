module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `MatExp.scaledRemainderFloat`, a bound on `E(r,η)` through a diagonal scaling

The remainder `E(r,η) = e^{|A|r} − Σᵢ₌₀^η (|A|r)ⁱ/i!` is bounded entry by entry by
`(s_j / s_k) τ`, `τ` the scalar remainder bound at the norm of `r N`, `N_jk = |a_jk| s_k / s_j`
(`Real.MatExp.expRemainderMat_le_scaled`). The norm is rounded up from the rounded-up entries;
`none` unless `2 ‖r N‖ ≤ η + 2` is certified, where the float bound `expRemainderBound` holds.
Scales that balance `|A|` keep `‖r N‖` small for a stiff oscillator, whose `‖r A‖` is in the
thousands; unit scales give the unscaled bound.

## Inputs
* `A` – float system matrix
* `s` – positive float scales
* `r` – nonnegative float step length
* `η` – Taylor order

## Output
* float matrix bounding `E(r,η)` from above, none if the scaled norm is too large for `η`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W_jk ≥ (s_j / s_k) · expRemainderBound ‖r N‖ η` where `2 ‖r N‖ ≤ η + 2`, else none. -/
def MatExp.scaledRemainderFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (r : 𝕋) (η : ℕ) :
    Option (Mat 𝕋 n n) :=
  let N : Mat 𝕋 n n := fun j k =>                                        -- r |a_jk| s_k / s_j
    mulUp (divUp (mulUp (absolute (A j k)) (s k)) (s j)) r
  let nrm := MatExp.normUpperBound (Interval.point N)                    -- ≥ ‖r N‖
  if le (addUp nrm nrm) (nsmulDown (η + 2) one) then                     -- ‖r N‖/(η+2) ≤ 1/2
    let τ := MatExp.expRemainderBound nrm η                              -- the scalar bound
    let W : Mat 𝕋 n n := fun j k => mulUp (divUp (s j) (s k)) τ          -- (s_j / s_k) τ
    some (Interval.point W).materialiseMat.sup                           -- stored, read n² times
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
