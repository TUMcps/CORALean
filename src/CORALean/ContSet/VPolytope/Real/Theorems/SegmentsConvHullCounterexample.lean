module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `[1, Eq. 30]` and `[1, Eq. 37]` at an empty operand

With [1, Table 3]'s `conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}`, `conv(∅, P) = ∅` — the paper's own
[1, Table 1 (conv)] says so. So `conv(⟨[]⟩, ⟨[0]⟩) = ∅`, while the concatenated list `⟨[0]⟩`
of [1, Eq. 30] is `{0}`, and the union `∅ ∪ {0}` of [1, Eq. 37] is not inside `∅`.

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.segments_convHull_counterexample :
    ∃ P₁ P₂ : VPolytope (Vec ℝ n),
      segments P₁.construct P₂.construct ≠ (P₁.convHull P₂).construct ∧
        ¬ P₁.construct ∪ P₂.construct ⊆ segments P₁.construct P₂.construct := by -- --- PROOF ---
  let P₁ : VPolytope (Vec ℝ n) := ⟨0, Fin.elim0⟩
  let P₂ : VPolytope (Vec ℝ n) := ⟨1, fun _ => 0⟩
  -- no point is a convex combination of an empty list
  have hseg : segments P₁.construct P₂.construct = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨_, ⟨β, _, hs, _⟩, _⟩ => by simp at hs
  have h0 : (0 : Vec ℝ n) ∈ P₂.construct := P₂.vertex_mem 0
  refine ⟨P₁, P₂, fun h => ?_, fun h => ?_⟩
  · have : (0 : Vec ℝ n) ∈ (P₁.convHull P₂).construct := by
      rw [VPolytope.convHull_exact]
      exact subset_convexHull ℝ _ (Or.inr h0)
    rw [← h, hseg] at this
    exact this
  · have := h (Or.inr h0)
    rw [hseg] at this
    exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
