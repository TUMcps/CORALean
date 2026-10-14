module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IsFullDimCora
public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# CORA's `polyZonotope/isFullDim` accepts a curve

The rank test says full-dimensional for `x = (a, a²)`, `a ∈ [-1, 1]`: `G = I`, `E = [1 2]`, no
independent generators. The generators span the plane, but the set is a parabola arc, which is
closed and has no interior point. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rank test holds for the arc `(a, a²)` of `ℝ²`, whose set has empty interior. -/
theorem PolyZonotope.isFullDim_cora_counterexample :
    ∃ pZ : PolyZonotope (Vec ℝ 2), pZ.isFullDimCora ∧
      ¬ (interior pZ.construct).Nonempty := by -- --- PROOF ---
  refine ⟨⟨1, 2, 0, 0, fun j => Pi.single j (1 : ℝ), fun _ j => (j : ℕ) + 1, Fin.elim0⟩, ?_, ?_⟩
  · -- the two unit vectors are generators, so the span is everything
    have hspan : Submodule.span ℝ (Set.range (fun j : Fin 2 => (Pi.single j (1 : ℝ) : Vec ℝ 2))
        ∪ Set.range (Fin.elim0 : Fin 0 → Vec ℝ 2)) = ⊤ := by
      refine top_unique ?_
      rw [← (Pi.basisFun ℝ (Fin 2)).span_eq]
      exact Submodule.span_mono (Set.subset_union_of_subset_left (by
        rintro _ ⟨j, rfl⟩; exact ⟨j, by simp⟩) _)
    show Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : Fin 2 => (Pi.single j (1 : ℝ) :
      Vec ℝ 2)) ∪ Set.range (Fin.elim0 : Fin 0 → Vec ℝ 2))) = _
    rw [hspan, finrank_top]
  · -- the set lies on the parabola `x₁ = x₀²`, and no ball does
    rintro ⟨y, hy⟩
    -- every point of the set is `(a, a²)`
    have hmem : ∀ x ∈ PolyZonotope.construct (⟨1, 2, 0, 0, fun j => Pi.single j (1 : ℝ),
        fun _ j => (j : ℕ) + 1, Fin.elim0⟩ : PolyZonotope (Vec ℝ 2)), x 1 = x 0 ^ 2 := by
      rintro x ⟨a, β, -, -, rfl⟩
      simp [PolyZonotope.monomial, Fin.sum_univ_two]
    -- a ball around `y` inside the set, and the point just above `y` in it
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    have hz : Function.update y 1 (y 1 + ε / 2) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro b
      fin_cases b
      · simpa using hε
      · simp
        rw [abs_of_pos hε]; linarith
    have h1 := hmem _ (hball hz)
    have h2 := hmem y (interior_subset hy)
    simp at h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
