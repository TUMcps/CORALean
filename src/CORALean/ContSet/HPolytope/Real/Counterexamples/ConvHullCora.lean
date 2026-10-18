module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.convHullCora`: `convHull_` as CORA's code computes it

`@polytope/convHull_.m` comments "convex hull with empty set is other set" (l. 63) and then
returns `polytope.empty(n)` when either operand represents the empty set (l. 64-67). Next the
fullspace exits (l. 70-76), then the 1-D and vertex-based computations (l. 79-97), which are a
parameter here (`rest`, not modelled). `representsa_(·, 'emptySet', eps)` reads as exact
emptiness. Read from the source, not run.

# CORA's polytope `convHull` with an empty operand returns the empty set

For `P = {x | x ≤ 0, -x ≤ -1}` (empty) and `S = [0, 1]`, the convex hull of `P ∪ S` is `S`, but
`@polytope/convHull_.m` exits with `polytope.empty(1)` as soon as one operand is empty
(`HPolytope.convHullCora`, whatever its later branches compute): `0` is missing.

## References

* [1] `contSet/@polytope/convHull_.m`, CORA, ll. 60-97.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The set [1] returns for two polytopes: the empty and fullspace exits, then `rest`. -/
noncomputable def HPolytope.convHullCora (P S : HPolytope (Vec ℝ n)) (rest : Set (Vec ℝ n)) :
    Set (Vec ℝ n) :=
  open Classical in
  -- l. 64-67: either operand `representsa_(·,'emptySet',eps)`, `P_out = polytope.empty(n)`
  if P.construct = ∅ ∨ S.construct = ∅ then ∅
  -- l. 70-76: either operand the fullspace, `P_out = polytope.Inf(n)`
  else if P.construct = Set.univ ∨ S.construct = Set.univ then Set.univ
  -- l. 79-97: the 1-D and vertex-based hulls (not modelled)
  else rest

end CORALean.Real

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

theorem HPolytope.convHullCora_empty_counterexample (rest : Set (Vec ℝ 1)) : -- --- STMT ---
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
