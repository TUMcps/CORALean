import CORALean.Specification.STL.Operations.UnsafeFactors
import Mathlib.Tactic.Linarith

/-!
# [1, Prop. 2]: a factor outside `K` reaches no point of the polytope

A reachable state `ξ = c + G(·,H) α̃ + G(·,K) β`, `|β| ≤ 1`, is what [1, Prop. 1] gives
(the proof's Eq. (25)). If `α̃` is not in `STL.unsafeFactors`, `C ξ ≤ d` fails: `ξ` is not in
`⟨C, d⟩_P`. This is the direction the model checking uses, an inclusion of the factors that meet
`P` in `K`, not an equality: a factor in `K` may still miss `P`, `K` being the box relaxation of
the uncertainty. Used for the time interval reachable set `R(τ_i)` too, with `N_i`, `M_i`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n s γ h p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.not_mem_of_not_mem_unsafeFactors (C : Matrix (Fin s) (Fin n) ℝ) (d : Fin s → ℝ)
    (c : Fin n → ℝ) (G : Matrix (Fin n) (Fin γ) ℝ) (H : Fin h → Fin γ) (K : Finset (Fin γ))
    (hp : h ≤ p) (α : Fin p → ℝ) (β : Fin γ → ℝ) (hβ : ∀ k ∈ K, |β k| ≤ 1) (ξ : Fin n → ℝ)
    (hξ : ∀ j, ξ j = c j + ∑ i, G j (H i) * α (Fin.castLE hp i) + ∑ k ∈ K, G j k * β k)
    (hα : α ∉ STL.unsafeFactors C d c G H K hp) : ¬ (∀ r, C.mulVec ξ r ≤ d r) := by -- --- PROOF ---
  intro hP
  apply hα
  intro r
  -- `C ξ` row `r` split along the three parts of `ξ`
  have e1 : ∑ j, C r j * ∑ i, G j (H i) * α (Fin.castLE hp i) =
      ∑ i, (C * G) r (H i) * α (Fin.castLE hp i) := by
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have e2 : ∑ j, C r j * ∑ k ∈ K, G j k * β k = ∑ k ∈ K, (C * G) r k * β k := by
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have key : C.mulVec ξ r = C.mulVec c r + ∑ i, (C * G) r (H i) * α (Fin.castLE hp i)
      + ∑ k ∈ K, (C * G) r k * β k := by
    simp only [Matrix.mulVec, dotProduct, hξ, mul_add, Finset.sum_add_distrib, e1, e2]
  have h1 := hP r
  -- the uncertain part is at least `-Σ|C G(·,k)|`, as `|β k| ≤ 1`
  have h2 : ∑ k ∈ K, -|(C * G) r k| ≤ ∑ k ∈ K, (C * G) r k * β k := by
    apply Finset.sum_le_sum
    intro k hk
    have : |(C * G) r k * β k| ≤ |(C * G) r k| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hβ k hk)
    linarith [neg_abs_le ((C * G) r k * β k)]
  rw [Finset.sum_neg_distrib] at h2
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
