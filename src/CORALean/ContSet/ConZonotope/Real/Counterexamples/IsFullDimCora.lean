module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `ConZonotope.isFullDimCora`

CORA's `@conZonotope/isFullDim` as the code computes it: without constraints the rank test of the
zonotope `(c, G)`; with them `T = null(A)`, `rank(G T) == n`. The null space `T` of the equality
rows is the set of coefficient vectors `ξ` with `Aₑ ξ = 0`, so the test asks that the generators
applied to it span all of `ℝⁿ`. Inequality rows (CORA has none) are not read, and `b` and the
unit box are not read either, which is why this is only a necessary condition for the set to have
an interior; see `isFullDim_cora_counterexample`.

# CORA's `conZonotope/isFullDim` accepts a point

The rank test `rank(G null(A)) == n` ignores that `|ξ| ≤ 1` together with `A ξ = b` can pin the
factors. With `c = 0`, `G = [1 0]`, `A = [1 1]`, `b = 2` in `ℝ¹` the only feasible factor vector is
`ξ = (1, 1)`, so the set is the point `{1}`; but `null(A)` is spanned by `(1, -1)`, `G (1, -1) = 1`
has rank `1 = n`, and CORA answers `true`. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's full-dimension test holds for a set with empty interior
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `rank(G T) = n` for `T` a basis of the null space of the equality rows. -/
def ConZonotope.isFullDimCora (cZ : ConZonotope (Vec ℝ n)) : Prop :=
  Module.finrank ℝ (Submodule.span ℝ
      {v : Vec ℝ n | ∃ ξ : Vec ℝ cZ.h, (∀ i, cZ.P.Ae i ξ = 0) ∧ v = ∑ j, ξ j • cZ.G j}) = n

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rank test holds for `c = 0`, `G = [1 0]`, `A = [1 1]`, `b = 2`: the set is `{1}`. -/
theorem ConZonotope.isFullDim_cora_counterexample : -- --- CONCL ---
    ∃ cZ : ConZonotope (Vec ℝ 1), cZ.isFullDimCora ∧
      ¬ (interior cZ.construct).Nonempty := by -- --- PROOF ---
  -- the data
  let G : Fin 2 → Vec ℝ 1 := ![fun _ => 1, fun _ => 0]
  let A : Mat ℝ 1 2 := fun _ _ => 1
  let cZ : ConZonotope (Vec ℝ 1) := ConZonotope.ofMat 0 G A (fun _ => 2)
  refine ⟨cZ, ?_, ?_⟩
  · -- `(t, -t)` is in the null space and `G (t, -t) = t`: the span is everything
    have hspan : Submodule.span ℝ
        {v : Vec ℝ 1 | ∃ ξ : Vec ℝ cZ.h, (∀ i, cZ.P.Ae i ξ = 0) ∧ v = ∑ j, ξ j • cZ.G j} = ⊤ := by
      refine top_unique fun v _ => Submodule.subset_span ⟨![v 0, -(v 0)], ?_, ?_⟩
      · intro i
        show (A *ᵥ ![v 0, -(v 0)]) i = 0
        simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · show v = ∑ j : Fin 2, (![v 0, -(v 0)] : Fin 2 → ℝ) j • G j
        funext k
        have hk : k = 0 := Subsingleton.elim _ _
        subst hk
        simp [Fin.sum_univ_two, G]
    show Module.finrank ℝ (Submodule.span ℝ
        {v : Vec ℝ 1 | ∃ ξ : Vec ℝ cZ.h, (∀ i, cZ.P.Ae i ξ = 0) ∧ v = ∑ j, ξ j • cZ.G j}) = 1
    rw [hspan, finrank_top]
    simp
  · -- the set is `{1}`, which has no interior point in `ℝ¹`
    rintro ⟨y, hy⟩
    -- every point of the set is `1`: the two factors are pinned by the box
    have hmem : ∀ x ∈ cZ.construct, x 0 = 1 := by
      rintro x ⟨β, hβ, hP, rfl⟩
      have h2 : β (0 : Fin 2) + β (1 : Fin 2) = 2 := by
        have := HPolytope.mem_eqs_iff.mp hP 0
        simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have h0 := abs_le.mp (hβ (0 : Fin 2))
      have h1 := abs_le.mp (hβ (1 : Fin 2))
      have e0 : β (0 : Fin 2) = 1 := by linarith [h0.2, h1.2]
      show ((0 : Vec ℝ 1) + ∑ j : Fin 2, β j • G j) 0 = 1
      simp [Fin.sum_univ_two, G, e0]
    -- a ball around `y` inside the set, and the point just above `y` in it
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    have hz : Function.update y 0 (y 0 + ε / 2) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro b
      have hb : b = 0 := Subsingleton.elim _ _
      subst hb
      simp
      rw [abs_of_pos hε]; linarith
    have h1 := hmem _ (hball hz)
    have h2 := hmem y (interior_subset hy)
    simp at h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
