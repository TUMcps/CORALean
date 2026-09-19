import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

/-!
# `Alg. 1`: reachability by abstraction in the state space

[1, Alg. 1] for ordinary differential equations, which is what [1] obtains
"by omitting each occurrence of the algebraic equation". One iteration of
lines 3-16 is `abstrStep`, the loop of lines 1-2 and 17 is `abstrRun`, and line
18's union is `abstrReach`.

Lines 4-5 are the caller's: `taylor` differentiates `f` and nothing in this
tree does, so `lin` hands back the `A` and `B` a linearization at the point
line 3 computed would give, exactly as `LinStep` carries them. That is also why
the certificate sits on the theorems and not here.

Three departures beyond that, all forced. Lines 8-11 may give out, so a run is
an `Option`. Line 2's `while` is no Lean recursion, so the caller supplies the
iteration count and a run that has reached `t_end` stands still. And line 18
unions the steps' sets, which is no zonotope, so `abstrReach` is a `Set`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure NonlinearSys.AbstrState (S : ℕ → Type) (n : ℕ) where
  /-- `t_k`, line 16. -/
  t : ℝ
  /-- `R(t_k)`, line 13, as line 15 last reduced it. -/
  R : S n
  /-- `R(τ_k)`, line 14, as line 15 last reduced it. -/
  Rτ : S n

/-- Line 1 and the algorithm's input `R(t_0) = X₀`, before the first iteration. -/
def NonlinearSys.abstrInit (X₀ : S n) : NonlinearSys.AbstrState S n :=
  { t := 0                                                       -- 1. k ← 0, t_k ← 0
    R := X₀
    Rτ := X₀ }

/-- Lines 3-16: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.abstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AbstrState S n) : Option (NonlinearSys.AbstrState S n) :=
  let zs := sys.linPoint Δt s.R U                                 -- 3. linPoint, eq. (6)
  let AB := lin zs.1 zs.2                                         -- 4.-5. taylor, linSys
  let lsys := NonlinearSys.linearize AB.1                         -- 5. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U                -- 5. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  let Rlint := lsys.timePointStep Δt ηlin s.R Ulin                -- 6. linReach, eq. (10)
  let Rlinτ := (lsys.timeIntervalStep Δt ηlin s.R)                -- 6. linReach, eq. (12)
    ⊞ lsys.inputSolution Δt ηlin Ulin
  let Ψ₀ := OfPoint.ofPoint (0 : Vec ℝ n)                         -- 7. Ψ ← 0
  match abstrErrLoop sub enlarge (Φ Rlinτ) Ψ₀ fuel with           -- 8.-11. the do-while
  | none => none
  | some Ψ =>
    let Rabs := lsys.inputSolution Δt ηabs Ψ                       -- 12. abstrSol, eq. (8)
    let Rt := Rlint ⊞ Rabs                                         -- 13. R(t_{k+1})
    let Rτ := Rlinτ ⊞ Rabs                                         -- 14. R(τ_{k+1})
    some { t := s.t + Δt,                                          -- 16. t ← t + Δt, k ← k + 1
           R := Reduce.reduce Rt o, Rτ := Reduce.reduce Rτ o }     -- 15. red

/-- Lines 2-17: iterate the step while `t_k < t_end`. -/
noncomputable def NonlinearSys.abstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tend : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.AbstrState S n)
  | 0 => some (NonlinearSys.abstrInit X₀)                          -- 1. initialize
  | k + 1 =>
    match sys.abstrRun U lin Φ sub enlarge Δt tend ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tend                                                -- 2. while t_k < t_end
      then sys.abstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def NonlinearSys.abstrReach (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tend : ℝ) (ηlin ηabs o fuel K : ℕ)
    (X₀ : S n) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ sys.abstrRun U lin Φ sub enlarge Δt tend ηlin ηabs o fuel X₀ (j + 1),
    construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
