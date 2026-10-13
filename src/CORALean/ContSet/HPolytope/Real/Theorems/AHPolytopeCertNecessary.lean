import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetIffOfInjective
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# When `[1, Thm. 1, Eq. 12]` is necessary

`[1, Thm. 2]`: the conditions are necessary if `range(H'ᵧ† Y') ⊕ ker(H'ᵧ) = ℝ^{qy}`
(`[1, Thm. 2, Eq. 18]`). `H'ᵧ†` is read through the one property the proof uses, `H'ᵧ H'ᵧ† = I`
(the Moore-Penrose inverse has it whenever `ker Hy = {0}`, as `[1, Def. 1]` requires).
Then `Y'` is onto: `w = H'ᵧ (H'ᵧ† w)`, and splitting `H'ᵧ† w` by `[1, Thm. 2, Eq. 18]` leaves
`w = Y' c`. So `Y` is injective, and `ahPolytope_subset_iff_of_injective` applies — which
is why `[1, Cor. 1]` follows: the hypothesis is the same.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx ny qx qy : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_cert_of_subset {xbar ybar : Vec ℝ n} {X : Mat ℝ n nx}
    {Y : Mat ℝ n ny} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy ny} {hy : Vec ℝ qy}
    (hfull : (interior (HPolytope.ineqs Hx hx).construct).Nonempty)
    (Hdag : Mat ℝ qy ny) (hdag : Hyᵀ * Hdag = 1)
    (h18 : ∀ u : Vec ℝ qy, ∃ (c : Vec ℝ n) (k : Vec ℝ qy),
      u = Hdag *ᵥ (Yᵀ *ᵥ c) + k ∧ Hyᵀ *ᵥ k = 0)
    (hsub : HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
        ⊆ HPolytope.ahPolytope ybar Y (HPolytope.ineqs Hy hy)) :
    ∃ (Γ : Mat ℝ ny nx) (β : Vec ℝ ny) (Λ : Mat ℝ qy qx), X = Y * Γ ∧
      ybar - xbar = Y *ᵥ β ∧ (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy * Γ ∧
      Λ *ᵥ hx ≤ hy + Hy *ᵥ β := by -- --- PROOF ---
  -- every `w` is `Y' c`: push `H'† w` through `[1, Thm. 2, Eq. 18]` and back through `H'`
  have honto : ∀ w : Vec ℝ ny, ∃ c, w = Yᵀ *ᵥ c := by
    intro w
    obtain ⟨c, k, hu, hk⟩ := h18 (Hdag *ᵥ w)
    refine ⟨c, ?_⟩
    have := congrArg (Hyᵀ *ᵥ ·) hu
    simp only [mulVec_mulVec, hdag, one_mulVec, mulVec_add, hk, add_zero] at this
    rwa [← Matrix.mul_assoc, hdag, Matrix.one_mul] at this
  -- so `Y v = 0` gives `v ⬝ v = c ⬝ Y v = 0`
  have hY : Function.Injective Y.mulVec := by
    intro v₁ v₂ h
    have h0 : Y *ᵥ (v₁ - v₂) = 0 := by rw [mulVec_sub, h, sub_self]
    obtain ⟨c, hc⟩ := honto (v₁ - v₂)
    have hdot : (v₁ - v₂) ⬝ᵥ (v₁ - v₂) = 0 := by
      conv_lhs => arg 1; rw [hc]
      rw [mulVec_transpose, ← dotProduct_mulVec, h0, dotProduct_zero]
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hdot)
  exact (HPolytope.ahPolytope_subset_iff_of_injective hY hfull).mp hsub

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
