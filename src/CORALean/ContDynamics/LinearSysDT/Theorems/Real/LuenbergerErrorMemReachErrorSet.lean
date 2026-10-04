import CORALean.ContDynamics.LinearSysDT.Definitions.ReachErrorSet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel
import Mathlib.Data.Matrix.Basic

/-!
# The Luenberger estimation error lies in its reachable set

[1, Thm. 2], the reachability step: with `x̂_0 = p₀` and `x_0 ∈ X₀ = ⟨p₀, H₀⟩`, every run of
`x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k`, `w_k ∈ W`, `v_k ∈ V`, has its error
`x_k - x̂_k` against the observer [1, Eq. 10] in `Ω_k` (Eq. 24 of [1, Thm. 2]). Subtracting the
observer from the system gives [1, Eq. 14], `e_{k+1} = (A - LC) e_k + E w_k - L F v_k`, and
unrolling it the theorem's Eq. 23. The box of its Eq. 21 is the hull of `Ω_k`
(`intervalEstimate_error_eq_hull`).

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.luenbergerError_mem_reachErrorSet (A : Mat ℝ n n) (B : Mat ℝ n nu)
    (C : Mat ℝ ny n) (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ nw)) (V : Zonotope (Vec ℝ nv))
    (u : ℕ → Vec ℝ nu) (y : ℕ → Vec ℝ ny) (x xh : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ nw)
    (v : ℕ → Vec ℝ nv) (h0 : x 0 ∈ X₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct) (hstep : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k + E *ᵥ w k)
    (hy : ∀ k, y k = C *ᵥ x k + F *ᵥ v k) (hxh0 : xh 0 = X₀.c)
    (hxh : ∀ k, xh (k + 1) = A *ᵥ xh k + B *ᵥ u k + L *ᵥ (y k - C *ᵥ xh k)) (k : ℕ) :
    x k - xh k ∈ LinearSysDT.reachErrorSet A C E F L X₀ W V k := by -- --- PROOF ---
  set M := A - L * C with hM
  set d : ℕ → Vec ℝ n := fun j => E *ᵥ w j + (-(L * F)) *ᵥ v j with hd
  -- [1, Eq. 14]: the error recursion
  have herr : ∀ j, x (j + 1) - xh (j + 1) = M *ᵥ (x j - xh j) + d j := fun j => by
    rw [hstep, hxh, hy, hM, hd]
    simp only [sub_mulVec, mulVec_sub, mulVec_add, ← mulVec_mulVec, neg_mulVec]
    abel
  -- its Eq. 23: its closed form
  have hclosed : ∀ j, x j - xh j = (M ^ j) *ᵥ (x 0 - xh 0) +
      ∑ m ∈ Finset.range j, (M ^ m) *ᵥ d (j - 1 - m) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [herr, ih, mulVec_add, mulVec_mulVec, ← pow_succ', Finset.sum_range_succ' _ j,
        mulVec_sum]
      simp only [mulVec_mulVec, ← pow_succ', pow_zero, one_mulVec]
      have : ∀ m ∈ Finset.range j, d (j - 1 - m) = d (j + 1 - 1 - (m + 1)) := fun m _ => by
        congr 1
        omega
      rw [Finset.sum_congr rfl fun m hm => by rw [this m hm]]
      abel
  -- the three parts of `Ω_k`
  have he0 : x 0 - xh 0 ∈ (⟨X₀.h, 0, X₀.G⟩ : Zonotope (Vec ℝ n)).construct := by
    obtain ⟨β, hβ, hx⟩ := h0
    exact ⟨β, hβ, by rw [hxh0, hx]; simp⟩
  have hsplit : ∑ m ∈ Finset.range k, (M ^ m) *ᵥ d (k - 1 - m) =
      ∑ m ∈ Finset.range k, (M ^ m * E) *ᵥ w (k - 1 - m) +
        ∑ m ∈ Finset.range k, (M ^ m * -(L * F)) *ᵥ v (k - 1 - m) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by simp only [hd, mulVec_add, mulVec_mulVec]
  rw [hclosed, hsplit, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨_, he0, rfl⟩ ?_) ?_
  · exact Set.finsetSum_mem_finsetSum _ _ _ fun m _ => ⟨_, hw _, rfl⟩
  · exact Set.finsetSum_mem_finsetSum _ _ _ fun m _ => ⟨_, hv _, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
