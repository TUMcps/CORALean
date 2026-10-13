module

public import CORALean.ContDynamics.LinearSys.Operations.NonlinearSysFloatModel
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float model of a linear system encloses it

`nonlinearSysFloatModel` encloses `sys.nonlinearSys`: the field's value lies in `A X ⊕ U`, and the
slope between two points is `A` and the identity, which the Jacobian boxes hold.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.nonlinearSysFloatModel_encloses (sys : LinearSys 𝕋 n) :
    sys.nonlinearSysFloatModel.Encloses sys.nonlinearSys where
  f_mem X U x hx u hu :=
    Interval.plus_outer _ _ ⟨_, Interval.mtimes_outer sys.A X ⟨x, hx, rfl⟩, u, hu, rfl⟩
  slope_mem X U x hx x' hx' u hu u' hu' := by
    -- the identity is stored exactly, so it reads as the identity matrix
    have h1 : toRealMat
        (fun i j : Fin n => if i = j then (FloatOps.one : 𝕋) else FloatOps.zero) = 1 := by
      funext i j
      by_cases hij : i = j
      · subst hij
        simp [toRealMat, toReal_one]
      · simp [toRealMat, hij, toReal_zero, Matrix.one_apply_ne hij]
    refine ⟨Scalar.toRealMat sys.A, Interval.mem_point sys.A, 1, ?_, ?_⟩
    · rw [← h1]
      exact Interval.mem_point _
    · -- `(A x + u) - (A x' + u') = A (x - x') + 1 (u - u')`
      simp only [LinearSys.nonlinearSys, Matrix.mulVec_sub, Matrix.one_mulVec]
      abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
