module

public import CORALean.ContDynamics.LinearSys.Operations.AutoStepFloat

@[expose] public section

/-!
# `Alg. 2` lines 4-31 in floats: the main loop

[1, Alg. 2]'s `autoRun` computed in `𝕋`: iterate `autoStepFloat` while `t_k < t_end`, at most
`K` times, and return the state it stopped at with the windows `R̂(τ_k)` of the iterations that
ran, each with the times `t_k, t_{k+1}` it covers (exactly, in ℚ). `none` propagates once the
tuning has given out at some step.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-31: up to `K` iterations from `s` while `t_k < t_end`, the state reached and the
windows `(t_k, t_{k+1}, R̂(τ_k))` of the iterations that ran. -/
def LinearSys.autoRunFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (tend : 𝕋)
    (εmax ζ : ℚ) (ηmax fuel : ℕ) :
    ℕ → LinearSys.AutoStateFloat 𝕋 n →
      Option (LinearSys.AutoStateFloat 𝕋 n × List (ℚ × ℚ × Zonotope (Vec 𝕋 n)))
  | 0, s => some (s, [])
  | K + 1, s =>
    if ToRat.toRat tend ≤ s.t then some (s, [])                         -- 4. until t_k ≥ t_end
    else do
      let (s', Rτk) ← sys.autoStepFloat X₀ V tend εmax ζ ηmax fuel s    -- 5.-31. one iteration
      let (s'', Rs) ← sys.autoRunFloat X₀ V tend εmax ζ ηmax fuel K s'  -- 4. the rest of the loop
      pure (s'', (s.t, s'.t, Rτk) :: Rs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
