module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.AffineDynamicsErrorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionErrorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionTauErrorFloat
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Alg. 2` lines 9-15 in floats: the order sweep

[1, Alg. 2]'s `autoTuneOrder` computed in `𝕋`: `η_k` sweeps upward from `2` until it clears both the
accumulating-error bound `ε^{a,τ}_k` (eq. 37) and the non-accumulating one `ε^{n,τ}_k`
(eq. 38). The errors are the float upper bounds `particularSolutionErrorFloat`,
`affineDynamicsErrorFloat` and `particularSolutionTauErrorFloat`, compared in ℚ through
`ToRat`, so exactly. The float remainder bound is sound only at an order its norm admits, so
an order is also asked to be admissible, as `adaptTimeStepOrderFloat` asks.

Which order comes out affects how tight the result is, never whether it is sound: the step
re-checks the order before it uses it (`autoStepFloat`). A NaN reads through `ToRat` as
`1.5 · 2 ^ 1024` and fails every comparison, so costs tightness only.

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

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 9-15: the coarsest `η ≥ 2` at which the order is admissible and both admissible-error
shares hold, `none` where the sweep gives out. -/
def LinearSys.autoTuneOrderFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
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
    else sys.autoTuneOrderFloat eAtk H ũ U₀ Δt εaτ εnτ (η + 1) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
