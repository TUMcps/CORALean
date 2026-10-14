module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrInit
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

@[expose] public section

/-!
# `Alg. 1` lines 3-15, linearizing at the centre

[1, Alg. 1]'s step. Line 3 is what separates this from `AbstrReach`'s
[2, Alg. 1]: [1] linearizes at `z✱(t_s) = center(R(t_s))`, [2] at
`linPoint`'s half step further along `f`. Line 3 names only `center(R(t_s))` though
`z = [xᵀ uᵀ]ᵀ`, so `center(U)` is taken for the input half, as [2, (6)]
prints. Lines 4-5 are otherwise the caller's, `taylor` differentiating `f`
where nothing here does, which is why the certificate sits elsewhere.

One departure, shared with `AbstrReach`: lines 7-10 may give out, so a step is
an `Option`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
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
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-15: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.centreAbstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.CentreAbstrState S n) : Option (NonlinearSys.CentreAbstrState S n) :=
  -- 3. z✱(t_s) ← center(R(t_s))
  let xs := Recentre.centre s.R
  -- 3. the input half of z✱
  let us := Recentre.centre U
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
  let Rlinτ := (lsys.timeIntervalStep Δt ηlin s.R)
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
