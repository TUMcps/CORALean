module

public import CORALean.ContDynamics.Conform.Operations.NarxAext
public import CORALean.ContDynamics.Conform.Operations.NarxBext
public import CORALean.ContDynamics.Conform.Operations.NarxE
public import CORALean.ContDynamics.Conform.Theorems.SumWindow
public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The window deviation of a linearized NARX model

[1, Cor. 2]: the first-order expansion of `y_k = h(y_{k-n_p:k-1}, u_{k-n_p:k})` along a
reference, with remainder `l_k`, is the recursion `δξ_{k+1} = A_ext,k δξ_k + ∑ᵢ B_ext,k,i δu_{k-i}
+ Eᵀ l_k` on the deviation `δξ_k = (y_{k-n_p} - ȳ_{k-n_p}, …, y_{k-1} - ȳ_{k-1})` of the
window, which `NonlinearARX.stack` reads at `k - n_p`. Unrolling it is [1, Cor. 2]'s GLO
matrices.

## Inputs
* `np` – number of lags
* `A` – output Jacobians
* `B` – input Jacobians
* `l` – remainders
* `y` – outputs
* `yb` – reference outputs
* `u` – inputs
* `ub` – reference inputs
* `k` – step

## Hypotheses
* `hy` – the Taylor expansion holds
* `hk` – step at least the number of lags

## Conclusion
* the window deviation moves by the extended matrices and the remainder

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 2]: the window deviation moves by `A_ext,k`, `B_ext,k,i` and `Eᵀ l_k`. -/
theorem Conform.narx_window_step (np : ℕ) (A : ℕ → ℕ → Mat ℝ ny ny) (B : ℕ → ℕ → Mat ℝ ny nu)
    (l : ℕ → Vec ℝ ny) (y yb : ℕ → Vec ℝ ny) (u ub : ℕ → Vec ℝ nu)
    (hy : ∀ k, np ≤ k → y k = yb k
      + ∑ i ∈ Finset.range np, A k (i + 1) *ᵥ (y (k - (i + 1)) - yb (k - (i + 1)))
      + ∑ i ∈ Finset.range (np + 1), B k i *ᵥ (u (k - i) - ub (k - i)) + l k)
    (k : ℕ) (hk : np ≤ k) : -- --- CONCL ---
    NonlinearARX.stack np y (k - np + 1) - NonlinearARX.stack np yb (k - np + 1)
      = Conform.narxAext np (A k) *ᵥ
          (NonlinearARX.stack np y (k - np) - NonlinearARX.stack np yb (k - np))
        + ∑ i ∈ Finset.range (np + 1),
            Conform.narxBext np (B k) i *ᵥ (u (k - i) - ub (k - i))
        + (Conform.narxE np ny)ᵀ *ᵥ l k := by -- --- PROOF ---
  funext r
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective r
  simp only [Pi.add_apply, Pi.sub_apply, NonlinearARX.stack, Equiv.symm_apply_apply,
    Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Conform.sum_window]
  simp only [Equiv.symm_apply_apply]
  by_cases h1 : a.val + 1 < np
  · -- a shift row: the next block of the old window
    have hB : ∀ (x : ℕ) (x_1 : Fin nu),
        Conform.narxBext np (B k) (x : ℤ) (finProdFinEquiv (a, i)) x_1 = 0 := by
      intro x x_1
      simp only [Conform.narxBext, Matrix.of_apply, Equiv.symm_apply_apply]
      rw [if_neg (by omega)]
    have hE : ∀ x, (Conform.narxE np ny)ᵀ (finProdFinEquiv (a, i)) x = 0 := by
      intro x
      simp only [Conform.narxE, Matrix.transpose_apply, Matrix.of_apply, Equiv.symm_apply_apply]
      rw [if_neg (by omega)]
    -- the input and remainder terms vanish in a shift row
    simp only [hB, hE, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Conform.narxAext, Matrix.of_apply, Equiv.symm_apply_apply, if_pos h1]
    -- only the block `a + 1` and the coordinate `i` meet the identity entry
    rw [Finset.sum_eq_single (⟨a.val + 1, h1⟩ : Fin np)
      (fun b _ hb => Finset.sum_eq_zero fun j _ => by
        rw [if_neg (by rintro ⟨h, _⟩; exact hb (Fin.ext h)), zero_mul]) (by simp)]
    rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [if_neg (by rintro ⟨_, h⟩; exact hj h), zero_mul]) (by simp)]
    rw [if_pos ⟨rfl, rfl⟩, one_mul, show k - np + 1 + a.val = k - np + (a.val + 1) by omega]
  · -- the last row: the expansion at `k`
    have h2 : a.val + 1 = np := by have := a.isLt; omega
    -- the expansion of `y k` at coordinate `i`
    have hy' := congrFun (hy k hk) i
    simp only [Pi.add_apply, Finset.sum_apply, Matrix.mulVec, dotProduct, Pi.sub_apply] at hy'
    rw [show k - np + 1 + a.val = k by omega, hy']
    have hE : ∑ x, (Conform.narxE np ny)ᵀ (finProdFinEquiv (a, i)) x * l k x = l k i := by
      simp only [Conform.narxE, Matrix.transpose_apply, Matrix.of_apply, Equiv.symm_apply_apply,
        h2, true_and]
      simp
    -- the extended input block is the plain block `B k x` in the last row
    have hB : ∀ x ∈ Finset.range (np + 1), ∑ x_1,
        Conform.narxBext np (B k) (x : ℤ) (finProdFinEquiv (a, i)) x_1 *
          (u (k - x) x_1 - ub (k - x) x_1)
        = ∑ x_1, B k x i x_1 * (u (k - x) x_1 - ub (k - x) x_1) := by
      intro x hx
      have hx' : x ≤ np := by have := Finset.mem_range.mp hx; omega
      simp only [Conform.narxBext, Matrix.of_apply, Equiv.symm_apply_apply, h2, and_true]
      have hc : (0 : ℤ) ≤ (x : ℤ) ∧ (x : ℤ) ≤ (np : ℤ) := ⟨by omega, by exact_mod_cast hx'⟩
      simp only [if_pos hc, Int.toNat_natCast]
    rw [hE, Finset.sum_congr rfl hB]
    have hA : ∑ b : Fin np, ∑ j : Fin ny, Conform.narxAext np (A k) (finProdFinEquiv (a, i))
          (finProdFinEquiv (b, j)) * (y (k - np + b) j - yb (k - np + b) j)
        = ∑ m ∈ Finset.range np, ∑ j,
            A k (m + 1) i j * (y (k - (m + 1)) j - yb (k - (m + 1)) j) := by
      simp only [Conform.narxAext, Matrix.of_apply, Equiv.symm_apply_apply, if_neg h1]
      -- the blocks run `0 … np - 1`, the lags `np … 1`
      rw [Fin.sum_univ_eq_sum_range (fun b => ∑ j : Fin ny, A k (np - b) i j *
        (y (k - np + b) j - yb (k - np + b) j)) np, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.mp hm
      rw [show np - (np - 1 - m) = m + 1 by omega,
        show k - np + (np - 1 - m) = k - (m + 1) by omega]
    rw [hA]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
