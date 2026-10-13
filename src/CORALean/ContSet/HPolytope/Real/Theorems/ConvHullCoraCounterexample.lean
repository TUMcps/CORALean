import CORALean.ContSet.HPolytope.Real.Operations.ConvHullCora
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# CORA's polytope `convHull` with an empty operand returns the empty set

For `P = {x | x ≤ 0, -x ≤ -1}` (empty) and `S = [0, 1]`, the convex hull of `P ∪ S` is `S`, but
`@polytope/convHull_.m` exits with `polytope.empty(1)` as soon as one operand is empty
(`HPolytope.convHullCora`, whatever its later branches compute): `0` is missing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `{x | lo ≤ x ≤ hi}` in `ℝ¹` by two halfspaces; empty when `hi < lo`. -/
def HPolytope.aux_convHullInterval (lo hi : ℝ) : HPolytope (Vec ℝ 1) where
  m := 2
  A := ![(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ), -(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ)]
  b := ![hi, -lo]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.convHullCora_empty_counterexample (rest : Set (Vec ℝ 1)) :
    let P := HPolytope.aux_convHullInterval 1 0
    let S := HPolytope.aux_convHullInterval 0 1
    (0 : Vec ℝ 1) ∈ convexHull ℝ (P.construct ∪ S.construct) ∧
      (0 : Vec ℝ 1) ∉ P.convHullCora S rest := by -- --- PROOF ---
  intro P S
  have hP : P.construct = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have h0 := hx.1 (show Fin 2 from 0)
    have h1 := hx.1 (show Fin 2 from 1)
    simp [P, HPolytope.aux_convHullInterval] at h0 h1
    linarith
  have hS : (0 : Vec ℝ 1) ∈ S.construct := by
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;> simp [S, HPolytope.aux_convHullInterval]
  refine ⟨subset_convexHull ℝ _ (Or.inr hS), ?_⟩
  simp [HPolytope.convHullCora, hP]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
