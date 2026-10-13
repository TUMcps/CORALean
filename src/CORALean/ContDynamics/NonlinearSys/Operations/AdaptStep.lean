module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptInit
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptLinPass
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneAbstrOrder

@[expose] public section

/-!
# `Alg. 2`: one adaptively-tuned step

[1, Alg. 2] for `k > 1`: line 1 updates the finite horizon from the last step's
gain, lines 2-15 run the step twice — once over the horizon, to get `R_abs(h)`
and from it the optimal step size, once over that step size, to get the
reachable set — and lines 16-18 report the gain, add the error and reduce.

`Φ` is indexed by the abstraction order `κ`, which is what lets line 13
compare the two orders eq. (47) weighs.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
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
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: one adaptively-tuned step, and `none` where an abstraction
error loop gave out. -/
noncomputable def NonlinearSys.adaptStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AdaptState S n) : Option (NonlinearSys.AdaptState S n) :=
  let hk := s.h * (ζδ - ζh) / (ζδ - s.φ)                          -- 1. h_k, eq. (59)
  let p₁ := sys.adaptLinPass U lin hk ηlin s.R                    -- 3.-6. a = 1, at Δt_k = h_k
  match abstrErrLoop sub enlarge (Φ s.κ p₁.2.2) (OfPoint.ofPoint 0) fuel with  -- 7. abstrErrLoop
  | none => none
  | some Ψh =>
    let rabs1 := rad ((NonlinearSys.linearize p₁.1).inputSolution hk ηabs Ψh)  -- 9. r⁽¹⁾_abs,k
    let ζA := Real.exp (Matrix.trace p₁.1 * hk)                   -- eq. (50)'s e^{tr(Ah)}
    let opt := optDeltat le ζδ ζZ ζA s.φ (rad s.R) rabs1 hk fuel  -- 10. optDeltat, Δt_k ← Δt*
    let p₂ := sys.adaptLinPass U lin opt.1 ηlin s.R               -- 3.-6. a = 2, at Δt_k = Δt*
    match abstrErrLoop sub enlarge (Φ 1 p₂.2.2) (OfPoint.ofPoint 0) fuel,      -- 7. abstrErrLoop,
      abstrErrLoop sub enlarge (Φ 2 p₂.2.2) (OfPoint.ofPoint 0) fuel with      --    at both orders
    | some Ψ₁, some Ψ₂ =>
      let lsys := NonlinearSys.linearize p₂.1
      let Rabs₁ := lsys.inputSolution opt.1 ηabs Ψ₁               -- 12. abstrSolAdaptive at κ = 1
      let Rabs₂ := lsys.inputSolution opt.1 ηabs Ψ₂               -- 12. abstrSolAdaptive at κ = 2
      let Rabs := if s.κ = 1 then Rabs₁ else Rabs₂                -- 12. R_abs(Δt*) at κ_k
      let rabsOpt := rad Rabs                                     -- 12. r^{(λ*)}_abs,k
      let κ' := tuneAbstrOrder le ζK s.φ rabsOpt s.rabs           -- 13. tuneAbstrOrder
        (dbox Rabs₁) (dbox Rabs₂) s.κ
      let φk := estimateGain le ζδ ((1 / ζδ) ^ opt.2) rabs1 rabsOpt opt.2 fuel -- 16. estimateGain
      let Rt := p₂.2.1 ⊞ Rabs                                     -- 17. R(t_{k+1})
      let Rτ := p₂.2.2 ⊞ Rabs                                     -- 17. R(τ_{k+1})
      some { t := s.t + opt.1, R := Reduce.reduce Rt o,           -- 18. redAdaptive
             Rτ := Reduce.reduce Rτ o, h := hk, φ := φk, κ := κ', rabs := rabsOpt }
    | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
