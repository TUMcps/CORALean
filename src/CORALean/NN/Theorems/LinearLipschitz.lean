module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# What a linear layer does to a distance

The constant is the largest row sum of `|W|`, which is the matrix's `ℓ∞`
operator norm — and `ℓ∞` is the metric a `Vec ℝ n` carries, being a pi type, so
no other norm would answer for the coordinates the rest of the development
reads. Mathlib's operator-norm instance is scoped and would have to displace
that one, so the bound is proved from the row directly.

The bias drops out: it is the same on both points, so only `W` enters.

Stated at the function rather than at `Layer.linear`, which needs three class
instances to even be written down and none of them to be Lipschitz.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipschitzWith_linear_eval (W : Mat ℝ m n) (b : Vec ℝ m) :
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
