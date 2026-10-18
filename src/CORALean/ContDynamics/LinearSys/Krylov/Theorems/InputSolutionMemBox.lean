module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpAugmentMulVec
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The Krylov error of the constant-input solution

[1, Lemma IV.1]: with `Ṽ, H̃` from Alg. 1 at `C̃ = [A u; 0 0]` and `ṽ = [0ₙ; 1]`, the solution
`x_p,const(δ) = ∫₀^δ e^{At}dt u` (18) lies in `P Ṽ e^{H̃δ} e₁ ⊕ [-1, 1]ⁿ ε̃ δ`, `P = [I 0ₙ]`.
`expIntegral A δ *ᵥ u` is that integral (`expIntegral_mulVec`). The proof is [1]'s: the first
`n` coordinates of `e^{C̃δ}ṽ` are `x_p,const(δ)` (`exp_augment_mulVec_castSucc`), and dropping
the last coordinate does not increase the error, of which (3) at `t = δ` (`‖ṽ‖ = 1`) is the
hypothesis, as for `Lemma III.1`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma IV.1]: `x_p,const(δ) ∈ P Ṽ e^{H̃δ} e₁ ⊕ [-1, 1]ⁿ ε̃ δ`, from (3) at `C̃, ṽ`. -/
theorem Krylov.inputSolution_mem_box (A : Mat ℝ n n) (u : Vec ℝ n) (V : Mat ℝ (n + 1) m)
    (H : Mat ℝ m m) (e₁ : Vec ℝ m) {ε δ : ℝ}
    (h3 : ‖exp (δ • Krylov.augment A u) *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ)
      - V *ᵥ (exp (δ • H) *ᵥ e₁)‖₂ ≤ ε * δ) : -- --- STMT ---
    ∃ r : Vec ℝ n, (∀ j, |r j| ≤ ε * δ) ∧
      MatExp.expIntegral A δ *ᵥ u
        = (fun j => (V *ᵥ (exp (δ • H) *ᵥ e₁)) (Fin.castSucc j)) + r := by -- --- PROOF ---
  refine ⟨MatExp.expIntegral A δ *ᵥ u - fun j => (V *ᵥ (exp (δ • H) *ᵥ e₁)) (Fin.castSucc j),
    fun j => ?_, by abel⟩
  -- the error at `j` is the augmented error at `castSucc j`, at most its Euclidean norm
  have h := abs_le_norm₂ (exp (δ • Krylov.augment A u)
    *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ) - V *ᵥ (exp (δ • H) *ᵥ e₁)) (Fin.castSucc j)
  rw [Pi.sub_apply, Krylov.exp_augment_mulVec_castSucc] at h
  exact h.trans h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
