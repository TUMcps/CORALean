module

public import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
public import CORALean.ContDynamics.LinearSys.Operations.AffineWindowFloat
public import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaTFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Operations.AutoTuneSetOrder
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Alg. 2` lines 4-31 in floats: one iteration of the main loop

`autoStep` computed in `𝕋`. `autoTuneDeltaTFloat` picks `Δt_k`, `η_k` (lines 5-15),
`Zonotope.autoTuneSetOrder` picks `ρ_k` (lines 19-22), then one step combines both with the
affine-dynamics update, lines 16-18 and 23-30. `V` is split `ũ ⊕ U₀` at its stored center (line
3). `[e^{At_k}]` and `[e^{At_{k+1}}]` are taken by scaling and squaring at their float brackets,
so `H(t_{k+1})` is reached from `X₀` directly, as line 26 reaches it. The tuned `(Δt_k, η_k)` is
checked before it is used (`Δt_k > 0`, `η_k ≥ 2`, `‖Δt_k A‖` admitted, no NaN), so the step is
sound at any pair the tuning returns (`autoStepFloat_outer`). Line 27 hats an `H(t_k)` no other
line produces; this uses the unhatted `H`. The curvature `C` is `MatExp.curvatureEnclosure`, floats.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `tend` – final float time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `s` – float loop state

## Output
* next float loop state and time-interval enclosure, if the tuning holds out

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-31: one iteration of [1, Alg. 2]'s main loop from `X₀` under inputs in `V`, the
next state and `R̂(τ_k)`, or `none` where the tuning at lines 5-15 or 19-22 gave out, the
tuned step is inadmissible, or no squaring count fits `[e^{At_k}]` or `[e^{At_{k+1}}]`. -/
def LinearSys.autoStepFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (tend : 𝕋)
    (εmax ζ : ℚ) (ηmax fuel : ℕ) (s : LinearSys.AutoStateFloat 𝕋 n) :
    Option (LinearSys.AutoStateFloat 𝕋 n × Zonotope (Vec 𝕋 n)) := do
  -- 3. {ũ}, V's stored center
  let ũ := (Interval.point V.c).zonotope
  -- 3. U₀ = V - ũ, holding 0
  let U₀ := Recenter.recenter V
  let ηe := max ηmax 2                                                 -- [e^{At_k}]'s order
  let sq ← sys.squaringsFloat s.Δt s.tLo s.tHi ηe                      -- t_k / 2^sq within Δt_{k-1}
  let eAtk := sys.expSquaringFloat s.tLo s.tHi ηe sq                   -- [e^{A t_k}]
  let Φtk := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{A t_k}] ·
    (S := 𝒵[𝕋]) eAtk
  -- 5.-15. Δt_k, η_k
  let (Δtk, ηk) ← sys.autoTuneDeltaTFloat eAtk s.H V.c s.t (ToRat.toRat tend) εmax ζ
    s.εa s.Δt ηmax fuel U₀
  let nrm := MatExp.normUpperBound (Interval.smul Δtk Δtk (Interval.point sys.A))  -- ≥ ‖Δt_k A‖
  if 0 < ToRat.toRat Δtk ∧ 2 ≤ ηk ∧ ToRat.toRat nrm / ((ηk : ℚ) + 2) ≤ 1 / 2   -- admissible
      ∧ ToRat.isNaN Δtk = false ∧ ToRat.isNaN nrm = false then              -- not read from a NaN
    -- 7. t_{k+1}
    let tk1 := s.t + ToRat.toRat Δtk
    -- 7. a float below t_{k+1}
    let tLo1 := addDown s.tLo Δtk
    -- 7. a float above t_{k+1}
    let tHi1 := addUp s.tHi Δtk
    let sq1 ← sys.squaringsFloat Δtk tLo1 tHi1 ηk                      -- t_{k+1} / 2^sq1 in Δt_k
    let Φtk1 := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{A t_{k+1}}] ·
      (S := 𝒵[𝕋])
      (sys.expSquaringFloat tLo1 tHi1 ηk sq1)
    -- 16. bPU_0(Δt_k), eq. (27)
    let bPU0Δt := Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm (Interval.point sys.A) Δtk 0) U₀
    -- 16. bPU_∞(Δt_k), eq. (27), with ⊕_i ÃᵢU₀ ⊕ E Δt_k U₀
    let bPUinfΔt := sys.inputTaylorSumTailFloat Δtk U₀ ηk ⊞
      Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputRemainder (Interval.point sys.A) Δtk ηk) U₀
    -- 17. e^{At_k}bPU_∞(Δt_k)
    let PUinfProp := Φtk bPUinfΔt
    -- 17. box(·)
    let PUinfBox := PUinfProp.interval.zonotope
    -- 17. P̂^U_∞(t_{k+1})
    let PUinf1 := s.PUinf ⊞ PUinfBox
    -- 18. P̂^U_0(t_{k+1})
    let PU01 := s.PU0 ⊞ Φtk bPU0Δt
    -- 19. eq. (35),(34)
    let εrτ := tk1 / ToRat.toRat tend * ζ * εmax - s.εr
    -- 20.-22. ρ_k
    let ρk ← PU01.autoTuneSetOrder εrτ 0 (PU01.h + 1)
    -- 23. P̂^U(t_{k+1})
    let PUk1 := Reduce.reduce PU01 ρk ⊞ PUinf1
    -- 24. P^u(Δt_k), eq. (19)
    let PuΔt := sys.inputSolutionFloat Δtk ηk ũ
    -- 25. P^u(t_{k+1}), a box
    let Puk1 := (s.Pu.zonotope ⊞ Φtk PuΔt).interval
    -- 26. H(t_{k+1})
    let Hk1 := Φtk1 X₀ ⊞ Puk1.zonotope
    -- 27.-28. Ĥ(τ_k)
    let Hτk := sys.affineWindowFloat s.H Hk1 V.c Δtk ηk
    -- 29. Δε^a_k, eq. (33)
    let Δεa := ToRat.toRat
      (sys.particularSolutionErrorFloat eAtk U₀ Δtk ηk)
    -- 29. ε^a_{k+1}
    let εa1 := s.εa + Δεa
    -- 29. Δε^r_k, Prop. 4
    let Δεr := ToRat.toRat (PU01.reduceBoxError ρk)
    -- 29. ε^r_{k+1}
    let εr1 := s.εr + Δεr
    -- 30. R̂(τ_k)
    let Rτk := Hτk ⊞ PUk1
    pure ({ t := tk1, tLo := tLo1, tHi := tHi1, Δt := Δtk, H := Hk1, Pu := Puk1, PU0 := PU01,
            PUinf := PUinf1, εa := εa1, εr := εr1 }, Rτk)
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
