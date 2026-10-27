module

public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptInit
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat
public import Mathlib.Data.Real.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Alg. 2`: one adaptively-tuned step

[1, Alg. 2] for `k > 1`: line 1 updates the finite horizon from the last step's
gain, lines 2-15 run the step twice — once over the horizon, to get `R_abs(h)`
and from it the optimal step size, once over that step size, to get the
reachable set — and lines 16-18 report the gain, add the error and reduce.

`Φ` is indexed by the abstraction order `κ`, which is what lets line 13
compare the two orders eq. (47) weighs.

## Inputs
* `sys` – system
* `U` – input set
* `lin` – linearization at a point
* `Φ` – true-error map
* `sub` – containment test
* `enlarge` – enlargement of the applied error
* `le` – comparison of reals
* `rad` – radius of a set
* `dbox` – box widths of a set
* `ζδ` – first tuning constant
* `ζh` – second tuning constant
* `ζZ` – third tuning constant
* `ζK` – fourth tuning constant
* `ηlin` – Taylor order of the linearization
* `ηabs` – Taylor order of the abstraction error
* `o` – zonotope order
* `fuel` – iteration bound
* `s` – loop state

## Output
* the next loop state, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Lines 3-6: the linearized system and the two sets it reaches, the half of
the loop body both passes share. -/
@[step_of NonlinearSys.adaptStep]
noncomputable def NonlinearSys.step_adaptLinPass (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Δt : ℝ) (ηlin : ℕ) (R : S n) :
    Mat ℝ n n × S n × S n :=
  let zs := sys.linPoint Δt R U                                   -- 3. linPoint, eq. (6)
  let AB := lin zs.1 zs.2                                         -- 4.-5. taylor, linSys
  let lsys := NonlinearSys.linearize AB.1                         -- 5. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U                -- 5. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  (AB.1, lsys.timePointStep Δt ηlin R Ulin,                       -- 6. linReachAdaptive, eq. (10)
    lsys.timeInterval Δt ηlin R ⊞ lsys.inputSolution Δt ηlin Ulin)  -- 6. eq. (12)

/-- [1, Alg. 2] line 13: the abstraction order of the next step, from the two
error radii of eq. (46) and the two diameter vectors of eq. (47). -/
@[step_of NonlinearSys.adaptStep]
noncomputable def step_tuneAbstrOrder (le : ℝ → ℝ → Bool) (ζK φstar rabs rabsLast : ℝ)
    (d1 d2 : Fin n → ℝ) (κ : ℕ) : ℕ :=
  -- 13. eq. (46): too close to re-tune
  if le |φstar * rabs / rabsLast| (1 - ζK) then κ
  else if ∀ i : Fin n, le (d1 i) 0 = true ∨ le ζK (d2 i / d1 i) = true
    -- 13. eq. (47): quadratic wins too little
    then 1
    -- 13. eq. (47): it is worth its cost
    else 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: one adaptively-tuned step, and `none` where an abstraction
error loop gave out. -/
noncomputable def NonlinearSys.adaptStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AdaptState S n) : Option (NonlinearSys.AdaptState S n) :=
  -- 1. h_k, eq. (59)
  let hk := s.h * (ζδ - ζh) / (ζδ - s.φ)
  -- 3.-6. a = 1, at Δt_k = h_k
  let p₁ := sys.step_adaptLinPass U lin hk ηlin s.R
  -- 7. abstrErrLoop
  match abstrErrLoop sub enlarge (Φ s.κ p₁.2.2) (OfPoint.ofPoint 0) fuel with
  | none => none
  | some Ψh =>
    -- 9. r⁽¹⁾_abs,k
    let rabs1 := rad ((NonlinearSys.linearize p₁.1).inputSolution hk ηabs Ψh)
    let ζA := Real.exp (Matrix.trace p₁.1 * hk)                   -- eq. (50)'s e^{tr(Ah)}
    -- 10. optDeltat, Δt_k ← Δt*
    let opt := optDeltat le ζδ ζZ ζA s.φ (rad s.R) rabs1 hk fuel
    -- 3.-6. a = 2, at Δt_k = Δt*
    let p₂ := sys.step_adaptLinPass U lin opt.Δt ηlin s.R
    -- 7. abstrErrLoop at both orders
    match abstrErrLoop sub enlarge (Φ 1 p₂.2.2) (OfPoint.ofPoint 0) fuel,
      abstrErrLoop sub enlarge (Φ 2 p₂.2.2) (OfPoint.ofPoint 0) fuel with
    | some Ψ₁, some Ψ₂ =>
      let lsys := NonlinearSys.linearize p₂.1
      -- 12. abstrSolAdaptive at κ = 1
      let Rabs₁ := lsys.inputSolution opt.Δt ηabs Ψ₁
      -- 12. abstrSolAdaptive at κ = 2
      let Rabs₂ := lsys.inputSolution opt.Δt ηabs Ψ₂
      -- 12. R_abs(Δt*) at κ_k
      let Rabs := if s.κ = 1 then Rabs₁ else Rabs₂
      -- 12. r^{(λ*)}_abs,k
      let rabsOpt := rad Rabs
      -- 13. step_tuneAbstrOrder
      let κ' := step_tuneAbstrOrder le ζK s.φ rabsOpt s.rabs
        (dbox Rabs₁) (dbox Rabs₂) s.κ
      -- 16. estimateGain
      let φk := estimateGain le ζδ ((1 / ζδ) ^ opt.exponent)
        rabs1 rabsOpt opt.exponent fuel
      -- 17. R(t_{k+1})
      let Rt := p₂.2.1 ⊞ Rabs
      -- 17. R(τ_{k+1})
      let Rτ := p₂.2.2 ⊞ Rabs
      -- 18. redAdaptive
      some { t := s.t + opt.Δt, R := Reduce.reduce Rt o,
             Rτ := Reduce.reduce Rτ o, h := hk, φ := φk, κ := κ', rabs := rabsOpt }
    | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
