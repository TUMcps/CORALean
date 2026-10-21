module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerLagrangeRemainder
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# The Lagrange remainder of the shear vanishes

(9) of [1] for the shear `f(x) = (x₂, 0)`, at any linearization point and over any region: `f`
is linear, its derivative constant, so `D²f ≡ 0`, every `max D²f⁽ⁱ⁾` is `0` and `[-l̂, l̂] = {0}`.
The remainder loop of [1, Alg. 1] (lines 10-13) thus stops at its first pass with `L̂ = 0`.

## Inputs
* `xstar` – linearization point
* `X` – region

## Hypotheses
* none

## Conclusion
* the Lagrange remainder is the origin

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- (9): `L = [0, 0]` for the linear `f(x) = (x₂, 0)`, as `D²f ≡ 0`. -/
theorem NonlinearSys.innerLagrangeRemainder_shear (xstar : Vec ℝ 2)
    (X : Set (Vec ℝ 2)) : -- --- CONCL ---
    NonlinearSys.innerLagrangeRemainder (fun x : Vec ℝ 2 => (![x 1, 0] : Vec ℝ 2)) xstar X =
      {0} := by -- --- PROOF ---
  let L : Vec ℝ 2 →L[ℝ] Vec ℝ 2 := LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 1; 0, 0])
  have hf : (fun x : Vec ℝ 2 => (![x 1, 0] : Vec ℝ 2)) = ⇑L := by
    funext y; ext i; fin_cases i <;> simp [L, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hD : fderiv ℝ (fderiv ℝ ⇑L) = 0 := by
    rw [show fderiv ℝ ⇑L = fun _ => L from funext fun _ => L.fderiv]
    funext y; exact fderiv_const_apply L
  simp only [NonlinearSys.innerLagrangeRemainder, hf, hD, Pi.zero_apply, _root_.zero_apply,
    abs_zero, Real.iSup_const_zero]
  have hl : (fun i : Fin 2 => (fun j => ⨆ y ∈ X, |y j - xstar j|) ⬝ᵥ
      ((fun _ _ => (0 : ℝ)) *ᵥ fun j => ⨆ y ∈ X, |y j - xstar j|) / 2) = 0 := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hl, neg_zero, Set.Icc_self]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
