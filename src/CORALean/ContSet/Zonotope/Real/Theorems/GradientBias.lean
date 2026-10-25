module

public import CORALean.ContSet.Zonotope.Real.Operations.Affine
public import CORALean.ContSet.Zonotope.Real.Theorems.DerivLine
public import CORALean.ContSet.Zonotope.Real.Theorems.FderivEqGradient
public import CORALean.ContSet.Zonotope.Real.Theorems.UpdateEqAddSingle

@[expose] public section

/-!
# The gradient of a set loss with respect to the biases

[1, Prop. 14]: through the layer `H_k = W_k H_{k-1} + b_k` the gradient of a set loss with respect
to the bias is `∇_{b_k} L = ∇_{H_k} L ⊙ ⟨1, 0⟩ᵀ`, with `Z₁ ⊙ Z₂ᵀ := c₁c₂ᵀ + G₁G₂ᵀ`, which is `c'_k ·
1 + G'_k · 0 = c'_k`: the derivative of the loss along `b_k(i)` is the center of the gradient set at
`i`. As in the paper's proof, `∂c_k(i)/∂b_k = e_i` and the generators do not depend on `b_k`; the
loss is differentiable at the layer's output in the center and generator entries together.

## Inputs
* `ℒ` – loss on zonotopes
* `W` – weight matrix
* `b` – bias vector
* `H` – input zonotope
* `i` – bias index

## Hypotheses
* `hF` – loss differentiable at the output

## Conclusion
* the bias derivative is the center of the gradient

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.gradient_bias (ℒ : Zonotope (Vec ℝ m) → ℝ) (W : Mat ℝ m n) (b : Vec ℝ m)
    (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) =>
      ℒ ⟨(H.affine W b).h, p.1, p.2⟩) ((H.affine W b).c, (H.affine W b).G))
    (i : Fin m) : -- --- CONCL ---
    deriv (fun t => ℒ (H.affine W (Function.update b i t))) (b i) =
      ((H.affine W b).gradient ℒ).c i := by -- --- PROOF ---
  set F : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) → ℝ :=
    fun p => ℒ ⟨(H.affine W b).h, p.1, p.2⟩ with hFdef
  -- moving `b(i)` moves the output center along the `i`-th basis vector
  have h1 : deriv (fun t => ℒ (H.affine W (Function.update b i t))) (b i) =
      fderiv ℝ F ((H.affine W b).c, (H.affine W b).G) (Pi.single i 1, 0) := by
    rw [← deriv_line F ((H.affine W b).c, (H.affine W b).G) (Pi.single i 1, 0) hF
      (b i)]
    congr 1
    funext t
    refine congrArg ℒ ?_
    show Zonotope.mk H.h (W *ᵥ H.c + Function.update b i t) (fun l => W *ᵥ H.G l) =
      Zonotope.mk H.h ((H.affine W b).c + (t - b i) • (Pi.single i 1 : Vec ℝ m))
        ((H.affine W b).G + (t - b i) • (0 : Fin (H.affine W b).h → Vec ℝ m))
    congr 1
    · rw [update_eq_add_single]
      show _ = W *ᵥ H.c + b + (t - b i) • (Pi.single i 1 : Vec ℝ m)
      abel
    · funext l
      show W *ᵥ H.G l = W *ᵥ H.G l + (t - b i) • (0 : Vec ℝ m)
      simp
  -- the derivative of the loss along that direction is the gradient's center
  refine h1.trans ?_
  rw [Zonotope.fderiv_eq_gradient ℒ (H.affine W b) hF]
  simp [single_dotProduct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
