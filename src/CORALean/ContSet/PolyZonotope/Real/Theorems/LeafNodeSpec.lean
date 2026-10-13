import CORALean.ContSet.PolyZonotope.Real.Operations.LeafNode

/-!
# A leaf node has an outgoing edge and no incoming one

`[1, Alg. 2]`, lines 4 and 5: the node `i` and target `j` that `leafNode` returns satisfy
`g i = some j`, and no node's edge ends at `i`.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: `leafNode` returns a node with an outgoing edge to `j` and no incoming edge. -/
theorem PolyZonotope.leafNode_spec (g : Fin h → Option (Fin h)) {i j : Fin h}
    (hl : PolyZonotope.leafNode g = some (i, j)) :
    g i = some j ∧ ∀ i', g i' ≠ some i := by -- --- PROOF ---
  unfold PolyZonotope.leafNode at hl
  obtain ⟨i₀, -, hi₀⟩ := List.exists_of_findSome?_eq_some hl
  by_cases hall : (List.finRange h).all (fun i' => g i' != some i₀) = true
  · rw [if_pos hall] at hi₀
    rcases hg : g i₀ with _ | j₀
    · rw [hg] at hi₀; simp at hi₀
    · rw [hg] at hi₀
      obtain ⟨rfl, rfl⟩ : i₀ = i ∧ j₀ = j := by simpa using hi₀
      refine ⟨hg, fun i' hi' => ?_⟩
      have := List.all_eq_true.mp hall i' (List.mem_finRange i')
      simp [hi'] at this
  · rw [if_neg hall] at hi₀
    simp at hi₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
