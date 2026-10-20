module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrState
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# `Alg. 1` line 18: the reachable set

`abstrReach`: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. Line 18 unions the steps' sets, which is no zonotope, so
this is a `Set`.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Output
* the union of the time-interval sets

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
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
def NonlinearSys.aux_abstrInit (X₀ : S n) : NonlinearSys.AbstrState S n :=
  { t := 0                                                       -- 1. k ← 0, t_k ← 0
    R := X₀
    Rτ := X₀ }

/-- Lines 3-16: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.aux_abstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AbstrState S n) : Option (NonlinearSys.AbstrState S n) :=
  -- 3. linPoint, eq. (6)
  let zs := sys.linPoint Δt s.R U
  -- 4.-5. taylor, linSys
  let AB := lin zs.1 zs.2
  -- 5. the linearized system
  let lsys := NonlinearSys.linearize AB.1
  -- 5. w ⊞ B(U ⊖ u✱)
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U
    (OfPoint.ofPoint (0 : Vec ℝ n))
  -- 6. linReach, eq. (10)
  let Rlint := lsys.timePointStep Δt ηlin s.R Ulin
  -- 6. linReach, eq. (12)
  let Rlinτ := (lsys.timeIntervalStep Δt ηlin s.R)
    ⊞ lsys.inputSolution Δt ηlin Ulin
  -- 7. Ψ ← 0
  let Ψ₀ := OfPoint.ofPoint (0 : Vec ℝ n)
  -- 8.-11. the do-while
  match abstrErrLoop sub enlarge (Φ Rlinτ) Ψ₀ fuel with
  | none => none
  | some Ψ =>
    -- 12. abstrSol, eq. (8)
    let Rabs := lsys.inputSolution Δt ηabs Ψ
    -- 13. R(t_{k+1})
    let Rt := Rlint ⊞ Rabs
    -- 14. R(τ_{k+1})
    let Rτ := Rlinτ ⊞ Rabs
    -- 16. t ← t + Δt, k ← k + 1
    some { t := s.t + Δt,
           -- 15. red
           R := Reduce.reduce Rt o, Rτ := Reduce.reduce Rτ o }

/-- Lines 2-17: iterate the step while `t_k < t_end`. -/
noncomputable def NonlinearSys.aux_abstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tend : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.AbstrState S n)
  | 0 => some (NonlinearSys.aux_abstrInit X₀)                          -- 1. initialize
  | k + 1 =>
    match sys.aux_abstrRun U lin Φ sub enlarge Δt tend ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tend                                                -- 2. while t_k < t_end
      then sys.aux_abstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. The horizon is `params.tFinal - params.tStart`, the loop's clock
starting at `0`. -/
noncomputable def NonlinearSys.abstrReach (sys : NonlinearSys n m)
    (params : Reach.InputParams (S n) (S m) ℝ) (options : NonlinearSys.AbstrReachOptions S n m) :
    Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  -- 2. the horizon of the loop, whose clock starts at `0`
  let tend := params.tFinal - params.tStart
  -- 18. `R([0,t_end])`, the union of the time-interval sets of iterations 1 to `K`
  ⋃ j < options.K, ⋃ s ∈ sys.aux_abstrRun U options.lin options.Φ options.sub options.enlarge
    options.Δt tend options.η options.taylorTermsAbstr options.ρ
    options.fuel X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
