module

public import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Definitions.SigmoidNetworks
public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ActivationPolyRefinable
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
public import CORALean.NN.Theorems.ActivationLipschitz
public import CORALean.NN.Theorems.EncloseAtInflate
public import CORALean.NN.Theorems.EvalLipschitz
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Lipschitz
public import CORALean.NN.Theorems.Real.LinearConvergent
public import CORALean.NN.Theorems.SigmoidLipschitz

@[expose] public section

/-!
# The network statement, at a network with three layers

`SigmoidRefinementConverges` discharges `IsConvergent` where the tail is empty and its Lipschitz
constant is `LipschitzWith.id`. Here neither is free: the head activation's residual passes through
a matrix and a second activation before it reaches the output, so the tail bound is a product of two
real constants and the `K` in `EncloseAtInflate` is what the refinement level is divided by. The
linear layer meets `IsConvergent` at every level, its propagation being exact, so the schedule
spends its levels on the two activations. This is [1, Thm. 4.14]'s hypothesis met where the tail is
not trivial.

## Inputs
* `W` – weight matrix
* `b` – bias vector

## Hypotheses
* none

## Conclusion
* the sigmoid, linear, sigmoid network is convergent

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise ContSet

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix

/-- What a linear layer does to a distance. -/
theorem Layer.aux_lipschitzWith_linear_eval (W : Mat ℝ m n) (b : Vec ℝ m) : -- --- CONCL ---
    LipschitzWith (Finset.univ.sup fun i => ∑ j, ‖W i j‖₊)
      (fun x : Vec ℝ n => W *ᵥ x + b) := by -- --- PROOF ---
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  have hK : (0:ℝ) ≤ ((Finset.univ.sup fun i => ∑ j, ‖W i j‖₊ : NNReal) : ℝ) :=
    NNReal.coe_nonneg _
  rw [dist_pi_le_iff (mul_nonneg hK hd)]
  intro i
  show dist ((W *ᵥ x + b) i) ((W *ᵥ y + b) i) ≤ _
  -- row `i` of the difference: the bias cancels and only the coordinates move
  have hdiff : (W *ᵥ x + b) i - (W *ᵥ y + b) i = ∑ j, W i j * (x j - y j) := by
    show (∑ j, W i j * x j) + b i - ((∑ j, W i j * y j) + b i) = ∑ j, W i j * (x j - y j)
    rw [Finset.sum_congr rfl fun j _ => mul_sub (W i j) (x j) (y j), Finset.sum_sub_distrib]
    ring
  -- and that row's sum of absolute values is under the supremum over all rows
  have hrow : ∑ j, |W i j| ≤ ((Finset.univ.sup fun i => ∑ j, ‖W i j‖₊ : NNReal) : ℝ) := by
    have hcoe : ((∑ j, ‖W i j‖₊ : NNReal) : ℝ) = ∑ j, |W i j| := by
      rw [NNReal.coe_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [coe_nnnorm, Real.norm_eq_abs]
    rw [← hcoe]
    exact NNReal.coe_le_coe.mpr
      (Finset.le_sup (f := fun i => ∑ j, ‖W i j‖₊) (Finset.mem_univ i))
  rw [Real.dist_eq, hdiff]
  calc |∑ j, W i j * (x j - y j)| ≤ ∑ j, |W i j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
    -- each coordinate moves at most `dist x y`, the supremum metric being that
    _ ≤ ∑ j, |W i j| * dist x y := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, ← Real.dist_eq]
        exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y j) (abs_nonneg _)
    _ = (∑ j, |W i j|) * dist x y := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hd

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidLinearSigmoidNetwork_convergent (W : Mat ℝ m n) (b : Vec ℝ m) : -- --- CONCL ---
    (Real.sigmoidLinearSigmoidNetwork W b).IsConvergent := by -- --- PROOF ---
  -- the last activation on its own, which is where the tail bound bottoms out
  have h₂ : (RefinableNetwork.cons (S := 𝒫𝒵)
      (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily
        Real.sigmoidPolyFamily_sound) .nil).HasLipschitzLayers :=
    ⟨⟨1, Layer.lipschitzWith_activation_eval lipschitzWith_sigmoid m⟩, trivial⟩
  -- and the matrix in front of it, whose constant is its largest row sum
  have h₁ : (RefinableNetwork.cons (S := 𝒫𝒵)
      ((Layer.linear W b).refinable (Layer.linear_encloses W b))
      (.cons (Real.Layer.activationPolyRefinable (n := m) Real.sigmoidPolyFamily
        Real.sigmoidPolyFamily_sound)
        .nil)).HasLipschitzLayers :=
    ⟨⟨_, Layer.aux_lipschitzWith_linear_eval W b⟩, h₂⟩
  exact ⟨Real.Layer.activationPolySigmoid_convergent n,
    RefinableNetwork.exists_lipschitzWith_eval _ h₁,
    Layer.linear_refinable_convergent W b,
    RefinableNetwork.exists_lipschitzWith_eval _ h₂,
    Real.Layer.activationPolySigmoid_convergent m, ⟨1, LipschitzWith.id⟩, trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
