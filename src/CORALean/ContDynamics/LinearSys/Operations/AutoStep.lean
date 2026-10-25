module

public import CORALean.ContDynamics.LinearSys.Definitions.AutoState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaT
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Operations.AutoTuneSetOrder

@[expose] public section

/-!
# `Alg. 2` lines 4-31: one iteration of the main loop

`autoStep`: [1, Alg. 2]. `autoTuneDeltaT` picks `Δt_k`, `η_k` (lines 5-15), `autoTuneSetOrder`
picks `ρ_k` (lines 19-22), then one step combines both with the affine-dynamics update, lines
16-18 and 23-30. `bPU_0(Δt_k)`/`bPU_∞(Δt_k)`, eq. (27)'s split of `bPU(Δt_k)`, are read as lines
17-18 use it: `e^{At_k}` multiplies each *afterward*, so `bPU_0 := Δt_k·U₀` and `bPU_∞ :=
⊕_{i=1}^η ÃᵢU₀ ⊕ E(Δt_k,η_k)Δt_kU₀`; `box(·)` (line 17) is `Zonotope.interval` after
`Interval.zonotope`, and `⊕_{i=1}^η ÃᵢU₀` is `inputTaylorSumTail`, the Minkowski sum (27)
prints. One correction: line 27 hats an `H(t_k)` no other line produces; `autoStep` uses the
unhatted `H`, matching Alg. 1's line 8.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `s` – loop state

## Output
* next loop state and time-interval set, if the tuning holds out

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-31: one iteration of [1, Alg. 2]'s main loop, `none` where the tuning at lines
5-15 or 19-22 gave out. -/
noncomputable def LinearSys.autoStep (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (tend εmax ζ : ℝ) (ηmax fuel : ℕ)
    (s : LinearSys.AutoState n) : Option (LinearSys.AutoState n × Zonotope (Vec ℝ n)) :=
  -- 3. ũ ← Bc_u + p
  let ũ := U.c
  -- 3. U₀ ← ⟨0,BG_u⟩_Z
  let U₀ : Zonotope (Vec ℝ n) := { h := U.h, c := 0, G := U.G }
  match sys.autoTuneDeltaT le s.H ũ s.t tend εmax ζ s.εa s.Δt ηmax fuel U₀ with
  -- 5.-15. gave out
  | none => none
  -- 5.-15. Δt_k, η_k
  | some (Δtk, ηk) =>
    -- 7. t_{k+1}
    let tk1 := s.t + Δtk
    let Φtk := exp (s.t • toRealMat sys.A)                             -- e^{A t_k}
    let Φtk1 := exp (tk1 • toRealMat sys.A)                            -- e^{A t_{k+1}}
    let A' := toRealMat sys.A
    -- 16. bPU_0(Δt_k), eq. (27)
    let bPU0Δt := Zonotope.mtimes (MatExp.particularCoeff A' Δtk 0) U₀
    -- 16. bPU_∞(Δt_k), eq. (27), with ⊕_{i=1}^{η_k} ÃᵢU₀
    let bPUinfΔt := Zonotope.plus
      (sys.inputTaylorSumTail (S := 𝒵) Δtk U₀ ηk)
      (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A' Δtk ηk) U₀)
    -- 17. e^{At_k}bPU_∞(Δt_k)
    let PUinfProp := Zonotope.mtimes Φtk bPUinfΔt
    -- 17. box(·)
    let PUinfBox := PUinfProp.interval.zonotope
    -- 17. P̂^U_∞(t_{k+1})
    let PUinf1 := Zonotope.plus s.PUinf PUinfBox
    -- 18. P̂^U_0(t_{k+1})
    let PU01 := Zonotope.plus s.PU0 (Zonotope.mtimes Φtk bPU0Δt)
    -- 19. eq. (35),(34)
    let εrτ := tk1 / tend * ζ * εmax - s.εr
    match Zonotope.autoTuneSetOrder le PU01 εrτ 0 (PU01.h + 1) with
    -- 20.-22. gave out
    | none => none
    -- 20.-22. ρ_k
    | some ρk =>
      -- 23. P̂^U(t_{k+1})
      let PUk1 := Zonotope.plus (Zonotope.reduce PU01 ρk) PUinf1
      -- 24. P^u(Δt_k), eq. (19)
      let PuΔt := sys.stepInputConst ũ Δtk
      -- 25. P^u(t_{k+1})
      let Puk1 := s.Pu + Φtk *ᵥ PuΔt
      -- 26. H(t_{k+1})
      let Hk1 := Zonotope.plus (Zonotope.mtimes Φtk1 X₀)
        (Zonotope.ofPoint Puk1)
      -- 27. C, eq. (15)-(16)
      let C := MatExp.curvatureEnclosure A' s.H ũ Δtk ηk
      -- 28. Ĥ(τ_k)
      let Hτk := Zonotope.plus (Zonotope.linComb s.H Hk1) C
      -- 29. Δε^a_k, eq. (33)
      let Δεa := MatExp.particularSolutionError A' s.t U₀.construct Δtk ηk
      -- 29. ε^a_{k+1}
      let εa1 := s.εa + Δεa
      -- 29. Δε^r_k, Prop. 4
      let Δεr := PU01.reduceBoxError ρk
      -- 29. ε^r_{k+1}
      let εr1 := s.εr + Δεr
      -- 30. R̂(τ_k)
      let Rτk := Zonotope.plus Hτk PUk1
      some ({ t := tk1, Δt := Δtk, H := Hk1, Pu := Puk1, PU0 := PU01, PUinf := PUinf1,
              εa := εa1, εr := εr1 }, Rτk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
