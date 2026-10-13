import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaHyperplaneCora
import Mathlib.Tactic.Linarith

/-!
# CORA's `polytope/representsa_(P, 'hyperplane')` accepts `ℝⁿ`

The unconstrained H-polytope (`polytope.Inf(n)`, no inequality and no equality rows) denotes
`ℝⁿ`. `isemptyobject` counts it as an empty object, and `representsa_emptyObject` answers
`'hyperplane'` with `true` for every empty object (written for the empty set of a vertex
representation), so `representsa(polytope.Inf(2),'hyperplane')` is `true`, though `ℝ²` is no
hyperplane. A wrong answer, not unsound. (`representsa_emptyObject` also answers `'convexSet'`
and `'levelSet'` with `false` for it, which `ℝⁿ` is.) Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `polytope.Inf(2)`: no rows. -/
def HPolytope.aux_noRows : HPolytope (Fin 2 → ℝ) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.aux_noRows_construct :
    HPolytope.aux_noRows.construct = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact ⟨fun i => i.elim0, fun i => i.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is `ℝ²`, which is no hyperplane `{x | f x = c}` with `f ≠ 0`; CORA answers `true`. -/
theorem HPolytope.representsa_hyperplane_cora_counterexample :
    HPolytope.aux_noRows.construct = Set.univ ∧
      (¬ ∃ (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        HPolytope.aux_noRows.construct = {x | f x = c}) ∧
      HPolytope.aux_noRows.representsaHyperplaneCora = true := by -- --- PROOF ---
  have hc := HPolytope.aux_noRows_construct
  refine ⟨hc, ?_, by simp [HPolytope.representsaHyperplaneCora, HPolytope.aux_noRows]⟩
  rintro ⟨f, c, hf, h⟩
  rw [hc] at h
  have hall : ∀ x, f x = c := fun x => by
    have : x ∈ ({x | f x = c} : Set (Fin 2 → ℝ)) := by rw [← h]; trivial
    exact this
  apply hf
  have h0 : c = 0 := by rw [← hall 0, map_zero]
  refine LinearMap.ext fun x => ?_
  rw [hall x, h0]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
