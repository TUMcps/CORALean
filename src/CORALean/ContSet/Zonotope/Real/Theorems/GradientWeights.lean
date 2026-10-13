module

public import CORALean.ContSet.Zonotope.Real.Operations.Affine
public import CORALean.ContSet.Zonotope.Real.Theorems.DerivLine
public import CORALean.ContSet.Zonotope.Real.Theorems.FderivEqGradient
public import CORALean.ContSet.Zonotope.Real.Theorems.UpdateEqAddSingle

@[expose] public section

/-!
# The gradient of a set loss with respect to the weights

[1, Prop. 14]: through the layer `H_k = W_k H_{k-1} + b_k` the gradient of a set loss with respect
to the weight matrix is `∇_{W_k} L = ∇_{H_k} L ⊙ H_{k-1}ᵀ`, with `Z₁ ⊙ Z₂ᵀ := c₁c₂ᵀ + G₁G₂ᵀ`: its
entry `(i, j)` is `c'_k(i) c_{k-1}(j) + Σₗ G'_k(i,l) G_{k-1}(j,l)`, the derivative of the loss along
that entry of `W_k`. As in the paper's proof, `∂c_k(i)/∂W_k(i,j) = c_{k-1}(j)` and `∂G_k(i,l)/
∂W_k(i,j) = G_{k-1}(j,l)`; the loss is differentiable at the layer's output in the centre and
generator entries together, which the paper takes for granted.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Setting the entry `(i, j)` of `W` to `t` moves `W v` along the `i`-th basis vector. -/
theorem Zonotope.aux_update_mulVec (W : Mat ℝ m n) (i : Fin m) (j : Fin n) (t : ℝ)
    (v : Vec ℝ n) :
    Function.update W i (Function.update (W i) j t) *ᵥ v =
      W *ᵥ v + (t - W i j) • (Pi.single i (v j) : Vec ℝ m) := by -- --- PROOF ---
  funext k
  by_cases hk : k = i
  · subst hk
    simp [mulVec, update_eq_add_single, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul,
      Pi.single_apply]
  · simp [mulVec, hk]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.gradient_weights (ℒ : Zonotope (Vec ℝ m) → ℝ) (W : Mat ℝ m n) (b : Vec ℝ m)
    (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) =>
      ℒ ⟨(H.affine W b).h, p.1, p.2⟩) ((H.affine W b).c, (H.affine W b).G))
    (i : Fin m) (j : Fin n) :
    deriv (fun t => ℒ (H.affine (Function.update W i (Function.update (W i) j t)) b)) (W i j) =
      ((H.affine W b).gradient ℒ).c i * H.c j +
        ∑ l, ((H.affine W b).gradient ℒ).G l i * H.G l j := by -- --- PROOF ---
  set F : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) → ℝ :=
    fun p => ℒ ⟨(H.affine W b).h, p.1, p.2⟩ with hFdef
  -- the direction in which the output zonotope moves with the entry `W(i, j)`
  let v : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) :=
    (Pi.single i (H.c j), fun l => Pi.single i (H.G l j))
  have h1 : deriv (fun t => ℒ (H.affine (Function.update W i (Function.update (W i) j t)) b))
      (W i j) = fderiv ℝ F ((H.affine W b).c, (H.affine W b).G) v := by
    rw [← deriv_line F ((H.affine W b).c, (H.affine W b).G) v hF (W i j)]
    congr 1
    funext t
    refine congrArg ℒ ?_
    show Zonotope.mk H.h (Function.update W i (Function.update (W i) j t) *ᵥ H.c + b)
        (fun l => Function.update W i (Function.update (W i) j t) *ᵥ H.G l) =
      Zonotope.mk H.h ((H.affine W b).c + (t - W i j) • v.1) ((H.affine W b).G + (t - W i j) • v.2)
    congr 1
    · rw [Zonotope.aux_update_mulVec]
      show _ = W *ᵥ H.c + b + (t - W i j) • Pi.single i (H.c j)
      abel
    · funext l
      rw [Zonotope.aux_update_mulVec]
      rfl
  -- the derivative of the loss along that direction is read off the gradient set
  refine h1.trans ?_
  rw [Zonotope.fderiv_eq_gradient ℒ (H.affine W b) hF]
  simp [single_dotProduct, mul_comm]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
