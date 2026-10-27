module

public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.CenterAbstrState
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# `Alg. 1` line 17, linearizing at the center

`centerAbstrReach`: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. Line 17's union is no zonotope, so this is a `Set`.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Output
* the union of the time-interval sets

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   30-September-2026
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Line 1 and the algorithm's input `R(t_0) = X₀`, before the first iteration. -/
def NonlinearSys.aux_centerAbstrInit (X₀ : S n) : NonlinearSys.CenterAbstrState S n :=
  { t := 0                                                       -- 1. s = 0, t_s = 0
    R := X₀
    Rτ := X₀ }

/-- Lines 3-15: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.aux_centerAbstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.CenterAbstrState S n) : Option (NonlinearSys.CenterAbstrState S n) :=
  -- 3. z✱(t_s) ← center(R(t_s))
  let xs := Recenter.center s.R
  -- 3. the input half of z✱
  let us := Recenter.center U
  -- 4. taylor
  let AB := lin xs us
  -- 4. the linearized system
  let lsys := NonlinearSys.linearize AB.1
  -- 4. w ⊞ B(U ⊖ u✱)
  let Ulin := linInput sys.f AB.1 AB.2 xs us U
    (OfPoint.ofPoint (0 : Vec ℝ n))
  -- 5. linReach, eq. (7)
  let Rlint := lsys.timePointStep Δt ηlin s.R Ulin
  -- 5. linReach, eq. (8)
  let Rlinτ := (lsys.timeInterval Δt ηlin s.R)
    ⊞ lsys.inputSolution Δt ηlin Ulin
  -- 6. Ψ = 0
  let Ψ₀ := OfPoint.ofPoint (0 : Vec ℝ n)
  -- 7.-10. the do-while
  match abstrErrLoop sub enlarge (Φ Rlinτ) Ψ₀ fuel with
  | none => none
  | some Ψ =>
    -- 11. abstrSol, eq. (6)
    let Rabs := lsys.inputSolution Δt ηabs Ψ
    -- 12. R(t_{s+1})
    let Rt := Rlint ⊞ Rabs
    -- 13. R(τ_{s+1})
    let Rτ := Rlinτ ⊞ Rabs
    -- 15. t ← t + Δt, s ← s + 1
    some { t := s.t + Δt,
           -- 14. red
           R := Reduce.reduce Rt o, Rτ := Reduce.reduce Rτ o }

/-- Lines 2-16: iterate the step while `t_s < t_K`. -/
noncomputable def NonlinearSys.aux_centerAbstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.CenterAbstrState S n)
  | 0 => some (NonlinearSys.aux_centerAbstrInit X₀)                    -- 1. initialize
  | k + 1 =>
    match sys.aux_centerAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tK                                                  -- 2. while t_s < t_K
      then sys.aux_centerAbstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 17: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. The horizon is `params.tFinal - params.tStart`, the loop's clock
starting at `0`. -/
noncomputable def NonlinearSys.centerAbstrReach (sys : NonlinearSys n m)
    (params : Reach.InputParams (S n) (S m) ℝ) (options : NonlinearSys.AbstrReachOptions S n m) :
    Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  -- 2. the horizon of the loop, whose clock starts at `0`
  let tK := params.tFinal - params.tStart
  -- 17. `R([0,t_K])`, the union of the time-interval sets of iterations 1 to `K`
  ⋃ j < options.K, ⋃ s ∈ sys.aux_centerAbstrRun U options.lin options.Φ options.sub options.enlarge
    options.Δt tK options.η options.taylorTermsAbstr options.ρ
    options.fuel X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
