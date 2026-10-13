module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

@[expose] public section

/-!
# `Alg. 2` lines 3-6: the half both passes share

`adaptLinPass`: [1, Alg. 2] lines 3-6, the linearized system and the two sets it reaches. Lines 4-5
are the caller's `lin`, as in `Alg. 1`.

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

/-- Lines 3-6: the linearized system and the two sets it reaches, the half of
the loop body both passes share. -/
noncomputable def NonlinearSys.adaptLinPass (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Δt : ℝ) (ηlin : ℕ) (R : S n) :
    Mat ℝ n n × S n × S n :=
  let zs := sys.linPoint Δt R U                                   -- 3. linPoint, eq. (6)
  let AB := lin zs.1 zs.2                                         -- 4.-5. taylor, linSys
  let lsys := NonlinearSys.linearize AB.1                         -- 5. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U                -- 5. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  (AB.1, lsys.timePointStep Δt ηlin R Ulin,                       -- 6. linReachAdaptive, eq. (10)
    lsys.timeIntervalStep Δt ηlin R ⊞ lsys.inputSolution Δt ηlin Ulin)  -- 6. eq. (12)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
