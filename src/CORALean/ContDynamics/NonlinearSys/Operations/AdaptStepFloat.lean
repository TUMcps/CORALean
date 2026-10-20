module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptInit
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPassFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OrderStepFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Alg. 2`: one adaptively-tuned step, in floats

[1, Alg. 2] for `k > 1` computed in `𝕋` from a `FloatHessModel`: line 1 updates the finite horizon
from the last step's gain, lines 2-15 run the step twice, once over the horizon to get `R_abs(h)`
and from it the optimal step size, once over that step size, and lines 16-18 report the gain, add
the error and reduce. The tuning is the real algorithm's, restated over `𝕋`; the abstraction
error is a checked region (`orderStepFloat`), not a fixed point (lines 7-11), so a step either
succeeds or the region check fails. The tuning cannot affect soundness: `adaptStepFloat_outer`
holds of whatever it chose.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `options` – reachability options
* `ζδ` – first tuning constant
* `ζh` – second tuning constant
* `ζZ` – third tuning constant
* `ζK` – fourth tuning constant
* `prec` – precision
* `bis` – bisection depth
* `fuel` – iteration bound
* `s` – loop state

## Output
* the next loop state, or none

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 2] line 13: the abstraction order of the next step, from the two
error radii of eq. (46) and the two diameter vectors of eq. (47). -/
def aux_tuneAbstrOrderFloat {n : ℕ} (ζK φstar rabs rabsLast : 𝕋) (d1 d2 : Fin n → 𝕋) (κ : ℕ) : ℕ :=
  if le (absolute (divUp (mulUp φstar rabs) rabsLast)) (subDown one ζK)
    -- 13. eq. (46): too close to re-tune
    then κ
  else if ∀ i : Fin n, le (d1 i) zero = true ∨ le ζK (divUp (d2 i) (d1 i)) = true
    -- 13. eq. (47): quadratic wins too little
    then 1
    -- 13. eq. (47): it is worth its cost
    else 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: one adaptively-tuned step, and `none` where a step's region check or the
first step's search gave out. The time `t` is kept exactly. -/
def NonlinearSys.FloatHessModel.adaptStepFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachOptions 𝕋) (ζδ ζh ζZ ζK : 𝕋) (prec bis fuel : ℕ)
    (s : NonlinearSys.AdaptState 𝒵[𝕋] n ℚ 𝕋) :
    Option (NonlinearSys.AdaptState 𝒵[𝕋] n ℚ 𝕋) := do
  let rad := fun (Z : Zonotope (Vec 𝕋 n)) =>                              -- radius of the box of Z
    maximumOver fun i => half (subUp (Z.interval.sup i) (Z.interval.inf i))
  let dia := fun (Z : Zonotope (Vec 𝕋 n)) (i : Fin n) =>  -- diameter of the box of Z
    subUp (Z.interval.sup i) (Z.interval.inf i)
  let opts := fun (Δt : 𝕋) => ({ options with Δt := Δt } : LinearSys.ReachOptions 𝕋)
  -- 1. h_k, eq. (59)
  let hk := divUp (mulUp s.h (subUp ζδ ζh)) (subDown ζδ s.φ)
  -- 3.-6. a = 1, at Δt_k = h_k
  let p₁ ← fm.toFloatModel.adaptLinPassFloat U (opts hk) s.R
  -- 7.-9. the step at κ_k
  let F₁ ← fm.orderStepFloat s.κ U (opts hk) s.R
  -- 9. r⁽¹⁾_abs,k
  let rabs1 := maximum zero (subUp (rad F₁.2) (rad p₁.2.1))
  let ζA := expUp prec (mulUp (sumUp fun i => p₁.1 i i) hk)         -- eq. (50)'s e^{tr(A)h}
  -- 10. optDeltat
  let opt := optDeltatFloat prec bis ζδ ζZ ζA s.φ (rad s.R) rabs1 hk fuel
  -- 3.-6. a = 2, at Δt_k = Δt*
  let p₂ ← fm.toFloatModel.adaptLinPassFloat U (opts opt.Δt) s.R
  -- 7.-12. the step at κ = 1
  let F₁' ← fm.orderStepFloat 1 U (opts opt.Δt) s.R
  -- 7.-12. the step at κ = 2
  let F₂' ← fm.orderStepFloat 2 U (opts opt.Δt) s.R
  -- 12. d(R_abs), κ = 1
  let dabs₁ := fun i => maximum zero (subUp (dia F₁'.2 i) (dia p₂.2.1 i))
  -- 12. d(R_abs), κ = 2
  let dabs₂ := fun i => maximum zero (subUp (dia F₂'.2 i) (dia p₂.2.1 i))
  -- 12. the step at κ_k
  let F := if s.κ = 1 then F₁' else F₂'
  -- 12. r^{(λ*)}_abs,k
  let rabsOpt := maximum zero (subUp (rad F.2) (rad p₂.2.1))
  -- 13. aux_tuneAbstrOrder
  let κ' := aux_tuneAbstrOrderFloat ζK s.φ rabsOpt s.rabs dabs₁ dabs₂ s.κ
  -- 16. estimateGain
  let φk := estimateGainFloat ζδ (powUp (divUp one ζδ) opt.exponent) rabs1 rabsOpt
    opt.exponent fuel
  -- 17. t_{k+1}
  pure { t := s.t + ToRat.toRat opt.Δt,
         -- 18. redAdaptive
         R := Reduce.reduce F.2 options.ρ,
         Rτ := Reduce.reduce F.1 options.ρ,
         h := hk, φ := φk, κ := κ', rabs := rabsOpt }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
