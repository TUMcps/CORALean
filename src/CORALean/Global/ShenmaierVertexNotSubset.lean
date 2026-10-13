import CORALean.Global.ShenmaierVertex

/-!
# Vertex sampling's `False` is certain

The first half of `[1, Thm. 4.6]`, for `[1, Alg. 3]`: `Ê ⊄ E` if `r_Svs > 1`. Each `zᵢ`
is in `B_p`, so `c + G zᵢ` is a point of `Ê`, and a value above `1` puts it outside `E`
(`coeffNorm_le_iff`). The second half — `P_Svs` as a probability that `Ê ⊆ E` — is not
formalized; see the paper's page.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E₁ E₂ V : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [AddCommGroup V]
  [Module ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaierVertex_eq_none_not_subset (G : E₁ →ₗ[ℝ] V) (c : V) (H : E₂ →ₗ[ℝ] V)
    (d : V) (n : ℕ) {N : ℕ} (hN : 0 < N) (z : Fin N → E₁)
    (hz : ∀ i, ‖z i‖ ≤ 1) (h : shenmaierVertex G c H d n hN z = none) :
    ¬ {x | ∃ α : E₁, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆
      {x | ∃ β : E₂, ‖β‖ ≤ 1 ∧ x = d + H β} := by -- --- PROOF ---
  have hgt : shenmaierVertexValue G c H d hN z > 1 := by
    unfold shenmaierVertex at h
    simp only at h
    split_ifs at h with hv
    exact hv
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    fun i => coeffNorm H (G (z i) + c - d)
  intro hsub
  -- `c + G zᵢ ∈ Ê` would be `d + H β` with `‖β‖ ≤ 1`, of norm at most `1`
  obtain ⟨β, hβ, he⟩ := hsub ⟨z i, hz i, rfl⟩
  have hle : coeffNorm H (G (z i) + c - d) ≤ 1 :=
    (coeffNorm_le_iff H ⟨β, by rw [add_comm (G (z i)), he]; abel⟩).mpr
      ⟨β, by rw [add_comm (G (z i)), he]; abel, hβ⟩
  unfold shenmaierVertexValue at hgt
  rw [hi] at hgt
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
