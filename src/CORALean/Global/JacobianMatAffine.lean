import CORALean.Global.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Jacobian of an affine map

`jacobianMat` of `z ↦ c + M z` is `M` at every point.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem jacobianMat_affine (c : Vec ℝ m) (M : Mat ℝ m n) (x : Vec ℝ n) :
    jacobianMat (fun z => c + M *ᵥ z) x = M := by -- --- PROOF ---
  -- the map is a constant plus a linear map, whose derivative is itself
  have h : HasFDerivAt (fun z : Vec ℝ n => c + M *ᵥ z)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).hasFDerivAt.const_add c
  unfold jacobianMat
  rw [h.fderiv]
  simp
  exact LinearMap.toMatrix'_toLin' M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
