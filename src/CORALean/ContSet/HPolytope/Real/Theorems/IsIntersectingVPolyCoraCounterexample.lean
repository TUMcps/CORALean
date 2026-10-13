module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.IsIntersectingVPolyCora
public import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's H/V-polytope intersection test reports disjoint polytopes as intersecting

The unit box `[-1, 1]²` in H-representation and the triangle `conv{(5,5), (6,5), (5,6)}` in
V-representation are disjoint, yet the program of `HPolytope.isIntersectingVPolyCora` is
feasible (`x = 0`, `β = (1, 0, 0)`): without `V β = x` it only asks that the H-polytope be
nonempty. Every `CORAlinprog` that returns `-2` only on an infeasible program therefore makes
`isIntersecting(P1,P2)` (default `'exact'`) answer `true`; no earlier branch of
`isIntersecting_.m` intercepts (neither set is a fullspace or a halfspace, `n = 2`, no equality).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isIntersectingVPolyCora_counterexample :
    let P1 : HPolytope (Vec ℝ 2) := HPolytope.ineqs !![1, 0; 0, 1; -1, 0; 0, -1] ![1, 1, 1, 1]
    let P2 : VPolytope (Vec ℝ 2) := ⟨3, ![![5, 5], ![6, 5], ![5, 6]]⟩
    Disjoint P1.construct P2.construct ∧
      ∀ linprog : Set (Vec ℝ 2 × (Fin P2.k → ℝ)) → ℤ, (∀ S, linprog S = -2 → S = ∅) →
        P1.isIntersectingVPolyCora P2 linprog = true := by -- --- PROOF ---
  intro P1 P2
  refine ⟨Set.disjoint_left.mpr fun x hx hx₂ => ?_, fun linprog hlp => ?_⟩
  -- `x₀ ≤ 1` in the box, `x₀ ≥ 5` in the triangle
  · have h0 := HPolytope.mem_ineqs_iff.mp hx 0
    obtain ⟨β, hβ, hs, rfl⟩ := hx₂
    simp [P2, mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] at h0 hs
    linarith [hβ 0, hβ 1, hβ 2]
  -- the program is feasible at `x = 0`, `β = (1, 0, 0)`
  · simp only [HPolytope.isIntersectingVPolyCora, bne_iff_ne, ne_eq]
    intro h
    have hne := hlp _ h
    have hz : ((0 : Vec ℝ 2), (![1, 0, 0] : Fin P2.k → ℝ)) ∈
        (∅ : Set (Vec ℝ 2 × (Fin P2.k → ℝ))) := by
      rw [← hne]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · rw [Fin.append_left, Fin.append_left]
          change Fin 4 at i
          fin_cases i <;> simp [P1, HPolytope.ineqs]
        · rw [Fin.append_right, Fin.append_right]
          change Fin 3 at j
          fin_cases j <;> simp
      · refine Fin.addCases (fun i => i.elim0) (fun _ => ?_) i
        simp [P2, Fin.sum_univ_three]
    exact hz

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
