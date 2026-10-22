module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `postΔ` in floats

`postDelta` computed in `𝕋`, [1, Sec. 4.1]'s `R∆(τs) = post∆(R(ts), Ψ(τs), A)` and
CORA's `Rdelta = Rhom + RV`: `aux_deltaReachFloat` for the homogeneous part, and for the
input set `V` what it contributes up to any time of the step. `V` is split at its
stored center as `reachFloatInput` splits it, so `0 ∈ V` is not asked: the
constant `ũ` contributes `inputSolutionFloat` of the segment `[0, ũ]`, the rest
`Ũ = V - ũ ∋ 0` its own `inputSolutionFloat`, each covering every time up to `Δt`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `R` – float start zonotope
* `V` – input float zonotope

## Output
* float zonotope of every state difference a step can span

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `enclose(0, ([e^{AΔt}] - I) R) ⊕ [F] R` at Taylor order `η`. -/
def LinearSys.aux_deltaReachFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η      -- [F]
  let eAΔtI := Interval.matPlus eAΔt (Interval.point (negIdentityMat 𝕋 n))  -- [e^{AΔt}] - I
  let O := (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope           -- the origin
  LinComb.linComb O (Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) eAΔtI R) ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- enclose(0, ·) ⊕ F R
      (S := 𝒵[𝕋]) F R


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state difference a step can span from `R` under inputs in `V`:
`aux_deltaReachFloat R ⊕ P̃^R([0, ũ]) ⊕ P^R(V - ũ)` at Taylor order `η`. -/
def LinearSys.postDeltaFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R V : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  sys.aux_deltaReachFloat Δt η R ⊞                                      -- Rhom
    (sys.inputSolutionFloat Δt η seg ⊞ sys.inputSolutionFloat Δt η Ũ)    -- RV

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
