module

public import CORALean.ContDynamics.LinearSys.Operations.AutoTuneSearch

@[expose] public section

/-!
# `Alg. 2` lines 5-15: the step size and the truncation order for one step

[1, Alg. 2]: line 5 doubles the previous step, then `autoTuneSearch` shrinks
and `autoTuneOrder` sweeps until both admissible-error bounds clear.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `H` – state zonotope
* `ũ` – constant input
* `tk` – step start time
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `εaAcc` – accumulated approximation error
* `Δtprev` – previous step length
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `U₀` – recentered input zonotope

## Output
* step size and order, if the halvings suffice

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] lines 5-15: `Δt_k`, `η_k`, or `none` where `fuel` halvings of `2·Δt_{k-1}`
did not suffice. -/
noncomputable def LinearSys.autoTuneDeltaT (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc Δtprev : ℝ) (ηmax fuel : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : Option (ℝ × ℕ) :=
  -- 5. Δt_k ← 2Δt_{k-1}
  let Δt₀ := 2 * Δtprev
  -- 6.-15. the repeat
  sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt₀ fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
