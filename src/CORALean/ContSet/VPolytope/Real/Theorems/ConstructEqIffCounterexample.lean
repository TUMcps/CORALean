import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
import CORALean.Global.DropIdx
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# `[1, Eq. 7]` with a repeated point

`⟨[0 0]⟩ = {0}` and `⟨[1 1]⟩ = {1}` differ, yet each point of either is redundant in its own
list — its copy is left — so the printed test answers `⊤`. `construct_eq_iff_of_injective` is the
test for lists without repeats.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_eq_iff_counterexample :
    ∃ P₁ P₂ : VPolytope (Vec ℝ 1),
      (∀ j, (∃ k, P₁.V j = P₂.V k) ∨
          P₁.V j ∈ (⟨P₁.k - 1, fun i => P₁.V (dropIdx j i)⟩ : VPolytope (Vec ℝ 1)).construct) ∧
        (∀ k, (∃ j, P₂.V k = P₁.V j) ∨
          P₂.V k ∈ (⟨P₂.k - 1, fun i => P₂.V (dropIdx k i)⟩ : VPolytope (Vec ℝ 1)).construct) ∧
        P₁.construct ≠ P₂.construct := by -- --- PROOF ---
  -- a list of two copies of `a`: dropping either leaves the other
  have hred : ∀ (a : Vec ℝ 1) (j : Fin 2),
      (fun _ : Fin 2 => a) j ∈ (⟨2 - 1, fun i => (fun _ : Fin 2 => a) (dropIdx j i)⟩ :
        VPolytope (Vec ℝ 1)).construct := fun a j =>
    VPolytope.vertex_mem (⟨2 - 1, fun _ => a⟩ : VPolytope (Vec ℝ 1)) ⟨0, by norm_num⟩
  refine ⟨⟨2, fun _ => 0⟩, ⟨2, fun _ => 1⟩, fun j => Or.inr (hred 0 j),
    fun k => Or.inr (hred 1 k), fun he => ?_⟩
  -- every point of `⟨[1 1]⟩` is `1`
  have h0 : (0 : Vec ℝ 1) ∈ (⟨2, fun _ => 1⟩ : VPolytope (Vec ℝ 1)).construct := by
    rw [← he]
    exact VPolytope.vertex_mem (⟨2, fun _ => 0⟩ : VPolytope (Vec ℝ 1)) 0
  obtain ⟨β, -, hs, hx⟩ := h0
  have := congrFun hx 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply,
    mul_one] at this
  rw [hs] at this
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
