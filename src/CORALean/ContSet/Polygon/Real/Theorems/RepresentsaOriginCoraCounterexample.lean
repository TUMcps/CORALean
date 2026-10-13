module

public import CORALean.ContSet.Polygon.Real.Operations.RepresentsaOriginCora
public import CORALean.ContSet.Polygon.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# CORA's `polygon/representsa_(pgon, 'origin')` accepts the empty polygon

`@polygon/representsa_.m` (l. 63) answers `'origin'` by `all(withinTol(vertices_(pgon),0,tol),
"all")`. The empty polygon has no vertices and `all([])` is `true`, so CORA reports `res = true`
(and `S = [0;0]`) for `polygon.empty()`, which denotes `∅`, not `{0}`. A wrong answer, not
unsound. Read from the source, not run. The same file answers `'emptySet'` by
`isempty(vertices_(pgon))`, so the empty polygon is reported both empty and the origin.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The empty polygon denotes `∅`; CORA nevertheless answers `'origin'` with `true`, though the
set is not `{0}`, and answers `'emptySet'` with `true` as well. -/
theorem Polygon.representsa_origin_cora_counterexample :
    Polygon.representsaOriginCora ⟨[]⟩ = true ∧
      Polygon.representsaEmptySet ⟨[]⟩ = true ∧
      ContSet.construct (⟨[]⟩ : Polygon) = (∅ : Set (Vec ℝ 2)) ∧
      ContSet.construct (⟨[]⟩ : Polygon) ≠ ({0} : Set (Vec ℝ 2)) := by -- --- PROOF ---
  have hc : ContSet.construct (⟨[]⟩ : Polygon) = (∅ : Set (Vec ℝ 2)) := by
    ext x
    simp [SetUnion.mem_construct]
  refine ⟨by simp [Polygon.representsaOriginCora, Polygon.vertices], by
    simp [Polygon.representsaEmptySet], hc, ?_⟩
  rw [hc]
  intro h
  have : (0 : Vec ℝ 2) ∈ (∅ : Set (Vec ℝ 2)) := by rw [h]; rfl
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
