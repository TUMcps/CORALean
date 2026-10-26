module

public import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
public import CORALean.ContSet.Interval.Real.Theorems.ExistsCoeffOfMem
public import CORALean.Global.Jacobian
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# The matrix zonotope of the Jacobians holds the Jacobian at every parameter of the box

The Jacobian of a map affine in `p` in the variable `z` is affine in `p` as well: center
`J f_0 + ∑ cᵢ J fᵢ`, generators `rᵢ J fᵢ`, with `J fᵢ = J f(·, eᵢ) - J f(·, 0)` as CORA's
`aux_parametric` forms it. So for every `p` of the box the Jacobian lies in the matrix zonotope
`linearize` builds. `z` is the state or the input: `zA` and `zB` are the two cases.

## Inputs
* `F` – map affine in the parameter
* `z` – point
* `I` – parameter box
* `p` – parameter vector

## Hypotheses
* `hAff` – the map is affine in the parameter
* `hd` – the map is differentiable at `z`
* `hp` – `p` lies in the box

## Conclusion
* the Jacobian at the parameter lies in the matrix zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {k n q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Jacobian of a map affine in a parameter. -/
private theorem aux_jacobianMat_sub (g h : Vec ℝ k → Vec ℝ n) (x : Vec ℝ k)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) : -- --- CONCL ---
    jacobianMat (fun z => g z - h z) x = jacobianMat g x - jacobianMat h x := by -- --- PROOF ---
  have h : HasFDerivAt (fun z => g z - h z) (fderiv ℝ g x - fderiv ℝ h x) x :=
    hg.hasFDerivAt.sub hh.hasFDerivAt
  unfold jacobianMat
  rw [h.fderiv]
  simp


/-- The Jacobian of a map affine in the parameter `p` is the Jacobian of `g0` plus the `p`-weighted
Jacobians of the `gi`, where all are differentiable. -/
private theorem aux_jacobianMat_param (g0 : Vec ℝ k → Vec ℝ n) (gi : Fin q → Vec ℝ k → Vec ℝ n)
    (p : Vec ℝ q) (x : Vec ℝ k) (h0 : DifferentiableAt ℝ g0 x)
    (hi : ∀ i, DifferentiableAt ℝ (gi i) x) : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.jacobianFamily_mem (F : Vec ℝ k → Vec ℝ q → Vec ℝ n)
    (hAff : ∀ z p, F z p = F z 0 + ∑ i, p i • (F z (Pi.single i 1) - F z 0)) (z : Vec ℝ k)
    (hd : ∀ p, DifferentiableAt ℝ (fun w => F w p) z) (I : Interval (Vec ℝ q)) {p : Vec ℝ q}
    (hp : p ∈ I.construct) : -- --- CONCL ---
    let Δ := fun i : Fin q => jacobianMat (fun w => F w (Pi.single i 1)) z - jacobianMat (fun w =>
      F w 0) z
    jacobianMat (fun w => F w p) z ∈
      (⟨q, jacobianMat (fun w => F w 0) z + ∑ i, I.center i •
          (Δ i),
        fun i => I.radius i • (Δ i)⟩ :
        Zonotope (Mat ℝ n k)).construct := by -- --- PROOF ---
  intro Δ
  obtain ⟨β, hβ, hpi⟩ := I.exists_coeff_of_mem hp
  refine ⟨β, hβ, ?_⟩
  -- the map is `F(·, 0) + ∑ pᵢ (F(·, eᵢ) - F(·, 0))`, so its Jacobian is that of the pieces
  have hmap : (fun w => F w p)
      = fun w => F w 0 + ∑ i, p i • (F w (Pi.single i 1) - F w 0) := funext fun w => hAff w p
  have hdi : ∀ i, DifferentiableAt ℝ (fun w => F w (Pi.single i 1) - F w 0) z :=
    fun i => (hd _).sub (hd 0)
  rw [hmap, aux_jacobianMat_param _ _ p z (hd 0) hdi]
  simp only [aux_jacobianMat_sub _ _ z (hd _) (hd 0)]
  -- split each parameter into the center's part and the generator's
  have hsum : ∀ i, p i • (Δ i)
      = I.center i • (Δ i)
        + β i • (I.radius i • (Δ i)) := fun i => by
    rw [hpi i, add_smul, mul_smul]
  simp only [Δ] at hsum ⊢
  simp only [Finset.sum_congr rfl fun i _ => hsum i, Finset.sum_add_distrib]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
