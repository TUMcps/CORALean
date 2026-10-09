import CORALean.Global.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The Jacobian of a map affine in a parameter

`z ↦ g₀(z) + ∑ᵢ pᵢ gᵢ(z)` has the Jacobian `J g₀ + ∑ᵢ pᵢ J gᵢ` wherever the `gᵢ` are
differentiable: the Jacobian is linear in the map. `jacobianMat_sub` is the difference case.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {k n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem jacobianMat_sub (g h : Vec ℝ k → Vec ℝ n) (x : Vec ℝ k) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    jacobianMat (fun z => g z - h z) x = jacobianMat g x - jacobianMat h x := by -- --- PROOF ---
  have h : HasFDerivAt (fun z => g z - h z) (fderiv ℝ g x - fderiv ℝ h x) x :=
    hg.hasFDerivAt.sub hh.hasFDerivAt
  unfold jacobianMat
  rw [h.fderiv]
  simp

theorem jacobianMat_param (g0 : Vec ℝ k → Vec ℝ n) (gi : Fin q → Vec ℝ k → Vec ℝ n)
    (p : Vec ℝ q) (x : Vec ℝ k) (h0 : DifferentiableAt ℝ g0 x)
    (hi : ∀ i, DifferentiableAt ℝ (gi i) x) :
    jacobianMat (fun z => g0 z + ∑ i, p i • gi i z) x
      = jacobianMat g0 x + ∑ i, p i • jacobianMat (gi i) x := by -- --- PROOF ---
  -- the derivative of the sum is the sum of the derivatives, scaled
  have h : HasFDerivAt (fun z => g0 z + ∑ i, p i • gi i z)
      (fderiv ℝ g0 x + ∑ i, p i • fderiv ℝ (gi i) x) x := by
    refine h0.hasFDerivAt.add ?_
    have := HasFDerivAt.sum (u := Finset.univ) (A := fun i => fun z => p i • gi i z)
      (A' := fun i => p i • fderiv ℝ (gi i) x) (fun i _ => (hi i).hasFDerivAt.const_smul (p i))
    simpa using this
  unfold jacobianMat
  rw [h.fderiv]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
