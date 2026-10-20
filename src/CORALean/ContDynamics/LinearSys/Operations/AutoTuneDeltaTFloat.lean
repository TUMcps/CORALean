module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.AffineDynamicsErrorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionErrorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionTauErrorFloat
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Alg. 2` lines 5-15 in floats: the step size and order

`autoTuneDeltaT` computed in `𝕋`: `Δt_k` and `η_k`, or `none` where `fuel` halvings of
`2·Δt_{k-1}` did not suffice. The tuned pair enters `autoStepFloat`, which re-checks it before
use, so the step is sound at any pair this returns: no soundness theorem is owed.

## Inputs
* `sys` – linear system
* `eAtk` – float exponential enclosure at the step start
* `H` – float state zonotope
* `ũ` – float constant input
* `tk` – step start time
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `εaAcc` – accumulated approximation error
* `Δtprev` – previous float step length
* `ηmax` – maximal Taylor order
* `fuel` – number of halvings
* `U₀` – recentered float input zonotope

## Output
* step size and order, if the halvings suffice

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 9-15: the coarsest `η ≥ 2` at which the order is admissible and both admissible-error
shares hold, `none` where the sweep gives out. -/
def LinearSys.aux_autoTuneOrderFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n) (U₀ : Zonotope (Vec 𝕋 n)) (Δt : 𝕋) (εaτ εnτ : ℚ) :
    ℕ → ℕ → Option ℕ
  | _, 0 => none
  | η, k + 1 =>
    let nrm := MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A))  -- ≥ ‖Δt A‖
    let Δεa := ToRat.toRat (sys.particularSolutionErrorFloat eAtk U₀ Δt η)       -- eq. (33)
    let Δεh := ToRat.toRat (sys.affineDynamicsErrorFloat H ũ Δt η)                -- eq. (23)
    let ΔεUτ := ToRat.toRat (sys.particularSolutionTauErrorFloat eAtk U₀ Δt η)    -- eq. (26)
    let Δεn := Δεh + ΔεUτ                                                         -- eq. (32)
    if le nrm (half (nsmulDown (η + 2) one)) && decide (Δεa ≤ εaτ) && decide (Δεn ≤ εnτ)
    then some η                                                          -- 15. both admissible
    else sys.aux_autoTuneOrderFloat eAtk H ũ U₀ Δt εaτ εnτ (η + 1) k

/-- Lines 6-15: halve `Δt` until `aux_autoTuneOrderFloat` finds an `η`, `none` after `fuel`
halvings without one. -/
def LinearSys.aux_autoTuneSearchFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n) (tk tend εmax ζ εaAcc : ℚ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec 𝕋 n)) : 𝕋 → ℕ → Option (𝕋 × ℕ)
  | _, 0 => none
  | Δt, k + 1 =>
    let Δt' := half Δt                                                      -- 7. Δt_k ← ½Δt_k
    let t1 := tk + ToRat.toRat Δt'                                          -- t_{k+1}
    let εaτ := t1 / tend * (1 - ζ) * εmax - εaAcc                           -- 14. eq. (37),(36)
    let εnτ := εmax - t1 / tend * ζ * εmax - εaAcc                          -- 14. eq. (38),(34)
    match sys.aux_autoTuneOrderFloat eAtk H ũ U₀ Δt' εaτ εnτ 2 ηmax with
    | some η => some (Δt', η)
    | none => sys.aux_autoTuneSearchFloat eAtk H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt' k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] lines 5-15: `Δt_k`, `η_k`, or `none` where `fuel` halvings did not suffice. -/
def LinearSys.autoTuneDeltaTFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n) (tk tend εmax ζ εaAcc : ℚ) (Δtprev : 𝕋) (ηmax fuel : ℕ)
    (U₀ : Zonotope (Vec 𝕋 n)) : Option (𝕋 × ℕ) :=
  -- 5. Δt_k ← 2Δt_{k-1}
  let Δt₀ := addUp Δtprev Δtprev
  -- 6.-15. the repeat
  sys.aux_autoTuneSearchFloat eAtk H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt₀ fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
