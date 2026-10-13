import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaIntervalCora
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# CORA's `polytope/representsa_(P, 'interval')` rejects the point `{0}`

`P = {0 ≤ x ≤ 2, 0 ≤ y ≤ 2, x + y ≤ 0}` is the point `(0, 0)`, the degenerate interval
`[0, 0]²`. CORA builds `I = [0, 2]²` from the axis-aligned rows; the row `x + y ≤ 0` has upper
support value `4 > 0` and lower value `0 ≤ 0`, so it "cuts through" and CORA returns
`representsa_(P, 'emptySet')`, which is `false` since `P` is nonempty. A false negative, not
unsound. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The square `[0, 2]²` cut by the row `x + y ≤ 0`. -/
def HPolytope.aux_squareCut : HPolytope (Fin 2 → ℝ) where
  m := 5
  A := let p0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    let p1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
    ![p0, -p0, p1, -p1, p0 + p1]
  b := ![2, 0, 2, 0, 0]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The polytope is the interval `[0, 0]²`, yet CORA does not accept it as an interval. -/
theorem HPolytope.representsa_interval_cora_counterexample :
    HPolytope.aux_squareCut.construct = Set.Icc (0 : Fin 2 → ℝ) 0 ∧
      ¬ HPolytope.aux_squareCut.representsaIntervalCora 0 (fun _ => 2) ![1, 1]
        0 := by -- --- PROOF ---
  -- the five rows pin both coordinates to `0`
  have hc : HPolytope.aux_squareCut.construct = Set.Icc (0 : Fin 2 → ℝ) 0 := by
    ext x
    constructor
    · rintro ⟨h, -⟩
      have h0 := h (0 : Fin 5)
      have h1 := h (1 : Fin 5)
      have h2 := h (2 : Fin 5)
      have h3 := h (3 : Fin 5)
      have h4 := h (4 : Fin 5)
      simp [HPolytope.aux_squareCut] at h0 h1 h2 h3 h4
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · rintro ⟨h0, h1⟩
      have a0 : x 0 = 0 := le_antisymm (h1 0) (h0 0)
      have a1 : x 1 = 0 := le_antisymm (h1 1) (h0 1)
      refine ⟨fun (i : Fin 5) => ?_, fun i => i.elim0⟩
      fin_cases i <;> simp [HPolytope.aux_squareCut, a0, a1]
  -- the cut row is neither redundant nor excluding, so CORA asks for emptiness; `0` is a point
  refine ⟨hc, fun h => ?_⟩
  have h0 : (0 : Fin 2 → ℝ) ∈ HPolytope.aux_squareCut.construct := by
    rw [hc]; exact ⟨le_rfl, le_rfl⟩
  unfold HPolytope.representsaIntervalCora at h
  simp [Fin.sum_univ_two] at h
  rw [h] at h0
  exact h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
