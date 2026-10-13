import CORALean.ContSet.Zonotope.Real.Operations.Affine
import CORALean.ContSet.Zonotope.Real.Theorems.DerivLine
import CORALean.ContSet.Zonotope.Real.Theorems.FderivEqGradient
import CORALean.ContSet.Zonotope.Real.Theorems.UpdateEqAddSingle

/-!
# The gradient set through a linear layer

[1, Prop. 13 (linear)]: through the layer `H_k = W_k H_{k-1} + b_k` the gradient set of a set
loss is `∇_{H_{k-1}} L = W_kᵀ ∇_{H_k} L`, `⟨W_kᵀ c'_k, W_kᵀ G'_k⟩`: the transpose applied to the
centre and to each generator column. As in the paper's proof, the loss depends on `H_{k-1}`
through `H_k`, so the chain rule reads `Σᵢ c'_k(i) ∂c_k(i) + Σᵢ Σⱼ G'_k(i,j) ∂G_k(j)(i)` with
`∂c_k(i)/∂c_{k-1}(j) = W_k(i,j)`; the loss is differentiable at the layer's output in the centre
and generator entries together, which the paper takes for granted.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.gradient_affine (ℒ : Zonotope (Vec ℝ m) → ℝ) (W : Mat ℝ m n) (b : Vec ℝ m)
    (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) =>
      ℒ ⟨(H.affine W b).h, p.1, p.2⟩) ((H.affine W b).c, (H.affine W b).G)) :
    H.gradient (fun Z => ℒ (Z.affine W b)) =
      { h := H.h
        c := Wᵀ *ᵥ ((H.affine W b).gradient ℒ).c
        G := fun l => Wᵀ *ᵥ ((H.affine W b).gradient ℒ).G l } := by -- --- PROOF ---
  set F : Vec ℝ m × (Fin (H.affine W b).h → Vec ℝ m) → ℝ :=
    fun p => ℒ ⟨(H.affine W b).h, p.1, p.2⟩ with hFdef
  -- the transpose applied to a gradient entry is a sum of its products with a column of `W`
  have hT : ∀ (j : Fin n) (x : Vec ℝ m), (Wᵀ *ᵥ x) j = (fun i => W i j) ⬝ᵥ x := fun j x => by
    simp [mulVec, dotProduct, transpose_apply]
  have hcol : ∀ (v : Vec ℝ n) (j : Fin n) (t : ℝ),
      W *ᵥ Function.update v j t = W *ᵥ v + (t - v j) • (fun i => W i j : Vec ℝ m) :=
    fun v j t => by
      rw [update_eq_add_single, mulVec_add, mulVec_smul, mulVec_single_one]; rfl
  unfold Zonotope.gradient
  congr 1
  · -- the centre: moving `c_j` moves the output centre along column `j` of `W`
    funext j
    -- the entry's derivative is the derivative of the loss along that column of `W`
    have h1 : deriv (fun t => ℒ ((({ H with c := Function.update H.c j t } :
        Zonotope (Vec ℝ n))).affine W b)) (H.c j) =
        fderiv ℝ F ((H.affine W b).c, (H.affine W b).G) (fun i => W i j, 0) := by
      rw [← deriv_line F ((H.affine W b).c, (H.affine W b).G) (fun i => W i j, 0)
        hF (H.c j)]
      congr 1
      funext t
      refine congrArg ℒ ?_
      show Zonotope.mk H.h (W *ᵥ Function.update H.c j t + b) (fun l => W *ᵥ H.G l) =
        Zonotope.mk H.h ((H.affine W b).c + (t - H.c j) • (fun i => W i j : Vec ℝ m))
          ((H.affine W b).G + (t - H.c j) • (0 : Fin (H.affine W b).h → Vec ℝ m))
      congr 1
      · rw [hcol]; simp only [Zonotope.affine]; abel
      · funext l
        show W *ᵥ H.G l = W *ᵥ H.G l + (t - H.c j) • (0 : Vec ℝ m)
        simp
    -- which is the `j`-th entry of `Wᵀ c'`
    show deriv _ (H.c j) = (Wᵀ *ᵥ ((H.affine W b).gradient ℒ).c) j
    rw [h1, Zonotope.fderiv_eq_gradient ℒ (H.affine W b) hF, hT]
    simp
  · -- the generators: moving `G_l(j)` moves the `l`-th output generator along column `j`
    funext l j
    let upd : ℝ → Zonotope (Vec ℝ n) := fun t =>
      { H with G := Function.update H.G l (Function.update (H.G l) j t) }
    -- the same along the generators
    have h1 : deriv (fun t => ℒ ((upd t).affine W b)) (H.G l j) =
        fderiv ℝ F ((H.affine W b).c, (H.affine W b).G)
          (0, Pi.single l (fun i => W i j : Vec ℝ m)) := by
      rw [← deriv_line F ((H.affine W b).c, (H.affine W b).G)
        (0, Pi.single l (fun i => W i j : Vec ℝ m)) hF (H.G l j)]
      congr 1
      funext t
      refine congrArg ℒ ?_
      show Zonotope.mk H.h (W *ᵥ H.c + b) (fun l' => W *ᵥ (Function.update H.G l
          (Function.update (H.G l) j t) l')) =
        Zonotope.mk H.h ((H.affine W b).c + (t - H.G l j) • (0 : Vec ℝ m))
          ((H.affine W b).G + (t - H.G l j) • (Pi.single l (fun i => W i j : Vec ℝ m) :
            Fin (H.affine W b).h → Vec ℝ m))
      congr 1
      · show _ = W *ᵥ H.c + b + (t - H.G l j) • (0 : Vec ℝ m)
        simp
      · -- only the `l`-th generator moves, by `(t - G_l(j))` times column `j`
        funext l'
        show W *ᵥ (Function.update H.G l (Function.update (H.G l) j t) l') =
          W *ᵥ H.G l' + (t - H.G l j) • ((Pi.single l (fun i => W i j : Vec ℝ m) :
            Fin (H.affine W b).h → Vec ℝ m) l')
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self, hcol]
          simp
        · have h0 : ((Pi.single l (fun i => W i j : Vec ℝ m) :
              Fin (H.affine W b).h → Vec ℝ m) l') = 0 := Pi.single_eq_of_ne hl _
          rw [Function.update_of_ne hl, h0]
          simp
    -- read off the gradient set: only the `l`-th generator's gradient is left
    refine h1.trans ?_
    show _ = (Wᵀ *ᵥ ((H.affine W b).gradient ℒ).G l) j
    rw [Zonotope.fderiv_eq_gradient ℒ (H.affine W b) hF, hT]
    simp only [zero_dotProduct, zero_add]
    rw [Finset.sum_eq_single (show Fin (H.affine W b).h from l)]
    · simp
    · intro l' _ hl'
      simp [hl']
    · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
