import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

/-!
# `Alg. 1`: reachability by abstraction, linearizing at the centre

[1, Alg. 1] for ordinary differential equations: lines 3-15 are `centreAbstrStep`, the
loop of lines 1-2 and 16 is `centreAbstrRun`, and line 17's union is `centreAbstrReach`.

Line 3 is what separates this from `AbstrReach`, which is [2, Alg. 1]: [1] linearizes at
`z✱(t_s) = center(R(t_s))`, [2] at `linPoint`'s half step further along `f`. The loop is
otherwise the same, but [1] numbers it in 17 lines and [2] in 18 — [2] splits `taylor`
and `linSys` where [1]'s line 4 does both — so from line 5 on the two numberings differ
by one, and one body cannot carry both without misleading one paper's reader.

Line 3 names only `center(R(t_s))` though `z = [xᵀ uᵀ]ᵀ`, so `center(U)` is taken for the
input half, as [2, (6)] prints. Lines 4-5 are otherwise the caller's, `taylor`
differentiating `f` where nothing here does, which is why the certificate sits elsewhere.

Three departures, all shared with `AbstrReach`: lines 7-10 may give out, so a run is an
`Option`; line 2's `while` is no Lean recursion, so the caller supplies the iteration
count and a run past `t_K` stands still; and line 17's union is no zonotope, so it is a `Set`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
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
structure NonlinearSys.CentreAbstrState (S : ℕ → Type) (n : ℕ) where
  /-- `t_s`, line 15. -/
  t : ℝ
  /-- `R(t_s)`, line 12, as line 14 last reduced it. -/
  R : S n
  /-- `R(τ_s)`, line 13, as line 14 last reduced it. -/
  Rτ : S n

/-- Line 1 and the algorithm's input `R(t_0) = X₀`, before the first iteration. -/
def NonlinearSys.centreAbstrInit (X₀ : S n) : NonlinearSys.CentreAbstrState S n :=
  { t := 0                                                       -- 1. s = 0, t_s = 0
    R := X₀
    Rτ := X₀ }

/-- Lines 3-15: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.centreAbstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.CentreAbstrState S n) : Option (NonlinearSys.CentreAbstrState S n) :=
  let xs := Recentre.centre s.R                                   -- 3. z✱(t_s) ← center(R(t_s))
  let us := Recentre.centre U                                     -- 3. the input half of z✱
  let AB := lin xs us                                             -- 4. taylor
  let lsys := NonlinearSys.linearize AB.1                         -- 4. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 xs us U                    -- 4. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  let Rlint := lsys.timePointStep Δt ηlin s.R Ulin                -- 5. linReach, eq. (7)
  let Rlinτ := (lsys.timeIntervalStep Δt ηlin s.R)                -- 5. linReach, eq. (8)
    ⊞ lsys.inputSolution Δt ηlin Ulin
  let Ψ₀ := OfPoint.ofPoint (0 : Vec ℝ n)                         -- 6. Ψ = 0
  match abstrErrLoop sub enlarge (Φ Rlinτ) Ψ₀ fuel with           -- 7.-10. the do-while
  | none => none
  | some Ψ =>
    let Rabs := lsys.inputSolution Δt ηabs Ψ                       -- 11. abstrSol, eq. (6)
    let Rt := Rlint ⊞ Rabs                                         -- 12. R(t_{s+1})
    let Rτ := Rlinτ ⊞ Rabs                                         -- 13. R(τ_{s+1})
    some { t := s.t + Δt,                                          -- 15. t ← t + Δt, s ← s + 1
           R := Reduce.reduce Rt o, Rτ := Reduce.reduce Rτ o }     -- 14. red

/-- Lines 2-16: iterate the step while `t_s < t_K`. -/
noncomputable def NonlinearSys.centreAbstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.CentreAbstrState S n)
  | 0 => some (NonlinearSys.centreAbstrInit X₀)                    -- 1. initialize
  | k + 1 =>
    match sys.centreAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tK                                                  -- 2. while t_s < t_K
      then sys.centreAbstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 17: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def NonlinearSys.centreAbstrReach (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel K : ℕ)
    (X₀ : S n) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ sys.centreAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ (j + 1),
    construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
