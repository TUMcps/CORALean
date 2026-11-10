module

public import CORALean.ContDynamics.NonlinearSys.Operations.VarphiTotalFloat
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `aux_varphiest` of CORA's `linReach_adaptive`, in floats

The gain `varphi` at the tuned step size CORA's `linReach_adaptive.m` estimates from the
abstraction errors at the finite horizon and at the step size, line by line: the ratio `rhs` of
their norms over the dimensions of lowest order, and the bisection on `[0, decrFactor^(minorder+1)]`
for the `varphi` whose total scaling (`varphiTotalFloat`) from the step size to the horizon meets
it, stopped at a residual below `1e-9` or a step below `1e-6`. CORA's `assert(rerr1 > rerrk)` and
its error after 10000 bisections are not modelled: `fuel` bounds the bisection. A tuning heuristic.

## Inputs
* `p` – precision of `sqrt`, `log`
* `horizon` – finite horizon
* `deltat` – tuned step size
* `abstrerrH` – error radii at the horizon
* `abstrerr` – error radii at the step size
* `decr` – `decrFactor`
* `mask` – the dimensions of lowest order
* `minorder` – lowest order
* `tolRes` – residual tolerance
* `tolStep` – step tolerance
* `fuel` – iteration bound

## Output
* the estimated gain
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The bisection: `varphi` between `low` and `up`, `prev` the last midpoint and `cnt` the count. -/
@[step_of NonlinearSys.varphiEstFloat]
def step_varphiBisect (p : ℕ) (rhs lim deltat horizon decr tolRes tolStep : 𝕋) :
    ℕ → ℕ → 𝕋 → 𝕋 → 𝕋 → 𝕋
  | 0, _, low, _, _ => low
  | fuel + 1, cnt, low, up, prev =>
    let mid := addUp low (half (subUp up low))                      -- low + 0.5*(up - low)
    let residual := subUp (NonlinearSys.varphiTotalFloat p mid lim deltat horizon decr) rhs
    let neg' := le zero residual = false                            -- residual < 0
    if le tolRes (absolute residual) = false ∨                      -- abs(residual) < 1e-9 or
      (0 < cnt ∧ le tolStep (absolute (subUp mid prev)) = false)    -- abs(varphi(cnt)-..) < 1e-6
    then mid
    else if neg' then step_varphiBisect p rhs lim deltat horizon decr tolRes tolStep fuel (cnt + 1)
      mid up mid
    else step_varphiBisect p rhs lim deltat horizon decr tolRes tolStep fuel (cnt + 1) low mid mid


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_varphiest`: the gain whose total scaling from `deltat` to `horizon` matches the
ratio of the abstraction errors in the lowest-order dimensions. -/
def NonlinearSys.varphiEstFloat (p : ℕ) (horizon deltat : 𝕋) (abstrerrH abstrerr : Vec 𝕋 n)
    (decr : 𝕋) (mask : Fin n → Bool) (minorder : ℕ) (tolRes tolStep : 𝕋) (fuel : ℕ) : 𝕋 :=
  let rerr1 := normUp p fun i => if mask i then abstrerrH i else zero  -- orders == minorder
  let rerrk := normUp p fun i => if mask i then abstrerr i else zero
  let rhs := divUp rerrk rerr1                                      -- rhs = rerrk / rerr1
  let lim := powUp decr (minorder + 1)                              -- varphi_lim
  step_varphiBisect p rhs lim deltat horizon decr tolRes tolStep fuel 0 zero lim zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
