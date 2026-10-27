module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineDynamicsError
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError

@[expose] public section

/-!
# `Alg. 2` lines 9-15: the order sweep

`η_k` sweeps upward from `2`, `I_i(Δt)` (eq. 17) being undefined below it, until it clears both
the accumulating-error bound `ε^{a,τ}_k` (eq. 37) and the non-accumulating one `ε^{n,τ}_k`
(eq. 38). One deliberate departure: [1]'s own `η_k` search (lines 8-12) is a *numerical* device,
tracking `T(j) := ⊕_{i=1}^j I_i(Δt)Aⁱ/i!` until its relative Frobenius-norm change is under
`10^{-10}`, decoupled from the bounds lines 13-15 check, and its index range does not typecheck
against eq. (17): at `i=1`, `I_1(Δt)`'s exponent `-1/(i-1)` divides by zero. `autoTuneOrder`
ties `η_k` directly to the bounds, sweeping against `le` as CDC'20's `adaptTimeStepOrder` does.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `H` – state zonotope
* `ũ` – constant input
* `tk` – step start time
* `U₀` – recentered input zonotope
* `Δt` – step length
* `εaτ` – accumulating error share
* `εnτ` – non-accumulating error share

## Output
* coarsest order meeting both error shares, if any

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 9-15, replacing the printed `T(j)`-convergence device (see module docstring): the
coarsest `η ≥ 2` at which both admissible-error shares hold, `none` where the sweep reaches
`ηmax` without one. -/
noncomputable def LinearSys.autoTuneOrder (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk : ℝ) (U₀ : Zonotope (Vec ℝ n))
    (Δt εaτ εnτ : ℝ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | η, k + 1 =>
    let Δεa := MatExp.particularSolutionError (toRealMat sys.A) tk U₀.construct Δt η  -- eq. (33)
    let Δεh := MatExp.affineDynamicsError (toRealMat sys.A) H ũ Δt η                  -- eq. (23)
    let ΔεUτ := MatExp.particularSolutionTauError (toRealMat sys.A) tk U₀.construct Δt η -- eq. (26)
    let Δεn := Δεh + ΔεUτ                                                             -- eq. (32)
    if (le Δεa εaτ && le Δεn εnτ) = true then some η                     -- 15. both admissible
    else LinearSys.autoTuneOrder sys le H ũ tk U₀ Δt εaτ εnτ (η + 1) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
