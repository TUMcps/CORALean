import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaPointCora
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# CORA's `polytope/representsa_(P, 'point')` accepts an empty polytope

`P = {x ≤ 0, -x ≤ -1}` in `ℝ²` (an H-representation, nonempty arrays, so
`representsa_emptyObject` does not catch it) is empty. For `'point'` and `n ≥ 2`, CORA reads
`[fulldim,subspace] = isFullDim(P)`, which for an empty polytope returns `false` and `[]`, and
sets `res = ~fulldim && isempty(subspace) = true`. A wrong answer, not unsound. Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The contradictory strip `{x ≤ 0, x ≥ 1}` in `ℝ²`. -/
def HPolytope.aux_emptyStrip : HPolytope (Fin 2 → ℝ) where
  m := 2
  A := let p0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    ![p0, -p0]
  b := ![0, -1]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.aux_emptyStrip_construct :
    HPolytope.aux_emptyStrip.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h, -⟩
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [HPolytope.aux_emptyStrip] at h0 h1
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The polytope is empty, so no single point; CORA answers `'point'` with `true`, whatever the
rest of `isFullDim` would compute. -/
theorem HPolytope.representsa_point_cora_counterexample (rest : Bool × List (Fin 2 → ℝ)) :
    HPolytope.aux_emptyStrip.construct = ∅ ∧
      (¬ ∃ p : Fin 2 → ℝ, HPolytope.aux_emptyStrip.construct = {p}) ∧
      HPolytope.aux_emptyStrip.representsaPointCora rest = true := by -- --- PROOF ---
  have hc := HPolytope.aux_emptyStrip_construct
  refine ⟨hc, ?_, ?_⟩
  · rintro ⟨p, hp⟩
    have : p ∈ HPolytope.aux_emptyStrip.construct := by rw [hp]; rfl
    rw [hc] at this
    exact this
  · simp [HPolytope.representsaPointCora, hc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
