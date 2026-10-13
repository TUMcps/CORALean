import CORALean.ContDynamics.LinearSys.Operations.AutoInitFloat
import CORALean.ContDynamics.LinearSys.Operations.AutoRunFloat

/-!
# `Alg. 2` in floats: reachability to a horizon

`ẋ = Ax + u`, `u(t) ∈ V` arbitrary in time, from `X₀` over `[0, t_end]`, by [1, Alg. 2] computed
in `𝕋`: `autoRunFloat` from `autoInitFloat` for at most `K` iterations, the windows
`R̂(τ_k)` with the times each covers, and `none` where the loop gave out or did not reach
`t_end` in `K` iterations. `V` is the input set in the state space, `B U`, split at its stored
centre. The horizon `t_end` must be a positive float.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the windows `(t_k, t_{k+1}, R̂(τ_k))` covering `[0, t_end]` from `X₀` under
inputs in `V`, or `none`. -/
def LinearSys.autoReachFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (tend : 𝕋)
    (εmax ζ : ℚ) (ηmax fuel K : ℕ) : Option (List (ℚ × ℚ × Zonotope (Vec 𝕋 n))) :=
  if 0 < ToRat.toRat tend ∧ ToRat.isNaN tend = false then               -- a positive horizon
    match sys.autoRunFloat X₀ V tend εmax ζ ηmax fuel K (LinearSys.autoInitFloat X₀ tend) with
    | none => none                                                      -- the tuning gave out
    | some (s, Rs) => if ToRat.toRat tend ≤ s.t then some Rs else none  -- 33. R̂([0,t_end])
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
