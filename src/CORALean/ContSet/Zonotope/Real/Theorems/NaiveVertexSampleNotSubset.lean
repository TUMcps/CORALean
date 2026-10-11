import CORALean.ContSet.Zonotope.Real.Theorems.NaiveVertexSampleLe

/-!
# Naive vertex sampling's `False` is certain

The first half of `[1, Cor. 4.7]`: `Ẑ ⊄ Ê` if `r_vs > 1`. A sampled corner is a point of `Ẑ`
(`Sec. III`), and a value above `1` puts it outside `E_q(H) + d` (`coeffNorm_le_iff`). The
second half, `Ẑ ⊆ Ê` "with probability at least `P_S(1 - r_vs)`", fails
(`Zonotope.naive_vertex_sample_printed_counterexample`).

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.naive_vertex_sample_not_subset (Z : Zonotope (Vec ℝ n)) (H : E →ₗ[ℝ] Vec ℝ n)
    (d : Vec ℝ n) (hN : (Finset.univ : Finset (Fin N)).Nonempty) (a : Fin N → Fin Z.h → Bool)
    (h : 1 < Finset.univ.sup' hN fun i => coeffNorm H (Z.corner (a i) - d)) :
    ¬ Z.construct ⊆ {x | ∃ β : E, ‖β‖ ≤ 1 ∧ x = d + H β} := by -- --- PROOF ---
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hN fun i => coeffNorm H (Z.corner (a i) - d)
  intro hsub
  -- a corner is a point of the zonotope
  have hmem : Z.corner (a i) ∈ Z.construct := by
    rw [Z.construct_eq_convexHull_corner]
    exact subset_convexHull ℝ _ ⟨a i, rfl⟩
  obtain ⟨β, hβ, he⟩ := hsub hmem
  have hle : coeffNorm H (Z.corner (a i) - d) ≤ 1 :=
    (coeffNorm_le_iff H ⟨β, by rw [he]; abel⟩).mpr ⟨β, by rw [he]; abel, hβ⟩
  rw [hi] at h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
