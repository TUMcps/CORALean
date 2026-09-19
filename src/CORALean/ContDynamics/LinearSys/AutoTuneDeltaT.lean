import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.AffineDynamicsError
import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionError
import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionTauError

/-!
# `Alg. 2` lines 5-15: the step size and the truncation order for one step

Shrink `Δt_k` from `2·Δt_{k-1}` by halving (line 7) until some `η_k` clears both the
accumulating-error bound `ε^{a,τ}_k` (eq. 37) and the non-accumulating one `ε^{n,τ}_k`
(eq. 38); `η_k` itself sweeps upward from `2`, `I_i(Δt)` (eq. 17) being undefined below it.

One departure, deliberate. [1]'s own `η_k` search (lines 8-12) is a *numerical* device —
track `T(j) := ⊕_{i=1}^j I_i(Δt)Aⁱ/i!` and stop once its relative Frobenius-norm change is
under `10^{-10}` — decoupled from the bounds lines 13-15 actually check, and its own index
range does not typecheck against eq. (17): at `i=1`, `I_1(Δt)`'s exponent `-1/(i-1)`
divides by zero. `autoTuneOrder` ties `η_k` directly to the bounds it must satisfy instead,
sweeping against `le` as CDC'20's `adaptTimeStepOrder` does, rather than a fixed tolerance
whose own printed index is ill-defined: a coarsest `η_k` inside both bounds, not a value
`T(j)` happens to have stabilized at.

Neither `Nat.find` nor `Classical.choose`: both sweeps go through `le` and are bounded
recursions with an explicit `fuel` — [1]'s own `Δt`-shrink has no stated bound either, so
`Option` is what a caller who runs out gets back.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

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

/-- Lines 6-15: halve `Δt` from the candidate line 5 doubled to, recomputing the two admissible
shares (eq. 37, eq. 38) at each new candidate, until `autoTuneOrder` finds an `η`. -/
noncomputable def LinearSys.autoTuneSearch (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc : ℝ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : ℝ → ℕ → Option (ℝ × ℕ)
  | _, 0 => none
  | Δt, k + 1 =>
    let Δt' := Δt / 2                                                       -- 7. Δt_k ← ½Δt_k
    let εaτ := (tk + Δt') / tend * (1 - ζ) * εmax - εaAcc                    -- 14. eq. (37),(36)
    let εnτ := εmax - (tk + Δt') / tend * ζ * εmax - εaAcc                   -- 14. eq. (38),(34)
    match LinearSys.autoTuneOrder sys le H ũ tk U₀ Δt' εaτ εnτ 2 ηmax with
    | some η => some (Δt', η)
    | none => LinearSys.autoTuneSearch sys le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt' k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] lines 5-15: `Δt_k`, `η_k`, or `none` where `fuel` halvings of `2·Δt_{k-1}`
did not suffice. -/
noncomputable def LinearSys.autoTuneDeltaT (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc Δtprev : ℝ) (ηmax fuel : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : Option (ℝ × ℕ) :=
  let Δt₀ := 2 * Δtprev                                                     -- 5. Δt_k ← 2Δt_{k-1}
  sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt₀ fuel            -- 6.-15. the repeat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
