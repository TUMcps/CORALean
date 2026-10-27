module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinusFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
public import CORALean.Global.Float.GenOpNorm

@[expose] public section

/-!
# `Δε^h_k(Δt, η)`, eq. (23), in floats

[1]'s eq. (23), `Real.MatExp.affineDynamicsError`, computed in `𝕋`:
`2 err(C) + √γ_h ‖G^{(-)}_h‖₂`, `C` the float `curvatureEnclosure`, `err` the Euclidean
`Zonotope.errUp`, `γ_h` the number of generators of `H` and `‖·‖₂` bounded from above by
`genOpNormUp` of the float `genMinus` at `[e^{AΔt}]`. A tuning quantity: the step is sound at
any value this takes.

## Inputs
* `sys` – linear system
* `H` – float state zonotope
* `ũ` – float constant input
* `Δt` – float step length
* `η` – Taylor order

## Output
* float upper bound of the affine dynamics error

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (23): `Δε^h_k(Δt, η) = 2 err(C) + √γ_h ‖G^{(-)}_h‖₂`, from above. -/
def LinearSys.affineDynamicsErrorFloat (sys : LinearSys 𝕋 n) (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : 𝕋 :=
  let C := MatExp.curvatureEnclosure (Interval.point sys.A) H ũ Δt η  -- C, eq. (15)-(16)
  let eAΔt := sys.expIntervalFloat Δt Δt η                              -- [e^{AΔt}]
  let γ := nsmulUp H.h one                                             -- γ_h, the generators of H
  addUp (addUp C.errUp C.errUp)                                        -- 2 err(C)
    (mulUp (sqrtUp 64 γ) (genOpNormUp 64 (MatExp.genMinus eAΔt H)))    -- √γ_h ‖G^{(-)}_h‖₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
