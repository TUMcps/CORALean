import CORALean.ContDynamics.LinearSys.Definitions.AutoState
import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaT
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Real.Operations.AutoTuneSetOrder

/-!
# `Alg. 2` lines 4-31: one iteration of the main loop

`autoStep`: [1, Alg. 2]. `autoTuneDeltaT` picks `Δt_k`, `η_k` (lines 5-15), `autoTuneSetOrder`
picks `ρ_k` (lines 19-22), then one step combines both with the affine-dynamics update, lines
16-18 and 23-30.

`bPU_0(Δt_k)`/`bPU_∞(Δt_k)`, eq. (27)'s split of `bPU(Δt_k)`, read the underbrace as lines
17-18 use it: `e^{At_k}` multiplies each *afterward*, so `bPU_0 := Δt_k·U₀` and `bPU_∞ :=
⊕_{i=1}^η ÃᵢU₀ ⊕ E(Δt_k,η_k)Δt_kU₀` carry no `e^{At_k}`. `box(·)` (line 17) is
`Zonotope.interval` after `Interval.zonotope`; `⊕_{i=1}^η ÃᵢU₀` is `inputTaylorSumTail`, the
Minkowski sum (27) prints and not the smaller `(Σ_i Ãᵢ)U₀` under the summed matrix.

One correction: line 27 hats an `H(t_k)` no other line produces — `H` is exact throughout and
line 28 reads it unhatted; `autoStep` uses the unhatted `H`, matching Alg. 1's line 8.

`Thm. 1` is a separate package; this file leaves `autoStep` `Option`-valued, `none` where a step
cannot satisfy `ε_max`, `ε^a_k`/`ε^r_k` named fields to induct on.

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
  let ũ := U.c                                                         -- 3. ũ ← Bc_u + p
  let U₀ : Zonotope (Vec ℝ n) := { h := U.h, c := 0, G := U.G }         -- 3. U₀ ← ⟨0,BG_u⟩_Z
  match sys.autoTuneDeltaT le s.H ũ s.t tend εmax ζ s.εa s.Δt ηmax fuel U₀ with
  | none => none                                                       -- 5.-15. gave out
  | some (Δtk, ηk) =>                                                  -- 5.-15. Δt_k, η_k
    let tk1 := s.t + Δtk                                               -- 7. t_{k+1}
    let Φtk := exp (s.t • toRealMat sys.A)                             -- e^{A t_k}
    let Φtk1 := exp (tk1 • toRealMat sys.A)                            -- e^{A t_{k+1}}
    let A' := toRealMat sys.A
    let bPU0Δt := Zonotope.mtimes (MatExp.particularCoeff A' Δtk 0) U₀ -- 16. bPU_0(Δt_k), eq. (27)
    let bPUinfΔt := Zonotope.plus                                      -- 16. bPU_∞(Δt_k), eq. (27)
      (sys.inputTaylorSumTail (S := 𝒵) Δtk U₀ ηk)                      --     ⊕_{i=1}^{η_k} ÃᵢU₀
      (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A' Δtk ηk) U₀)
    let PUinfProp := Zonotope.mtimes Φtk bPUinfΔt                      -- 17. e^{At_k}bPU_∞(Δt_k)
    let PUinfBox := PUinfProp.interval.zonotope                        -- 17. box(·)
    let PUinf1 := Zonotope.plus s.PUinf PUinfBox                       -- 17. P̂^U_∞(t_{k+1})
    let PU01 := Zonotope.plus s.PU0 (Zonotope.mtimes Φtk bPU0Δt)       -- 18. P̂^U_0(t_{k+1})
    let εrτ := tk1 / tend * ζ * εmax - s.εr                            -- 19. eq. (35),(34)
    match Zonotope.autoTuneSetOrder le PU01 εrτ 0 (PU01.h + 1) with
    | none => none                                                     -- 20.-22. gave out
    | some ρk =>                                                       -- 20.-22. ρ_k
      let PUk1 := Zonotope.plus (Zonotope.reduce PU01 ρk) PUinf1       -- 23. P̂^U(t_{k+1})
      let PuΔt := sys.stepInputConst ũ Δtk                             -- 24. P^u(Δt_k), eq. (19)
      let Puk1 := s.Pu + Φtk *ᵥ PuΔt                                   -- 25. P^u(t_{k+1})
      let Hk1 := Zonotope.plus (Zonotope.mtimes Φtk1 X₀)               -- 26. H(t_{k+1})
        (Zonotope.ofPoint Puk1)
      let C := MatExp.curvatureEnclosure A' s.H ũ Δtk ηk               -- 27. C, eq. (15)-(16)
      let Hτk := Zonotope.plus (Zonotope.linComb s.H Hk1) C            -- 28. Ĥ(τ_k)
      let Δεa := MatExp.particularSolutionError A' s.t U₀.construct Δtk ηk -- 29. Δε^a_k, eq. (33)
      let εa1 := s.εa + Δεa                                            -- 29. ε^a_{k+1}
      let Δεr := PU01.reduceBoxError ρk                                -- 29. Δε^r_k, Prop. 4
      let εr1 := s.εr + Δεr                                            -- 29. ε^r_{k+1}
      let Rτk := Zonotope.plus Hτk PUk1                                -- 30. R̂(τ_k)
      some ({ t := tk1, Δt := Δtk, H := Hk1, Pu := Puk1, PU0 := PU01, PUinf := PUinf1,
              εa := εa1, εr := εr1 }, Rτk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
