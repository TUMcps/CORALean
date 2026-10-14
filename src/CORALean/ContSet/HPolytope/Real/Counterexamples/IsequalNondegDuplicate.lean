module

public import CORALean.ContSet.HPolytope.Real.Operations.IsequalNondeg
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `HPolytope.isequalNondeg` needs the minimal representation

The test lets an unmatched row pass when it is redundant in its own polytope, one row at a time.
A row listed twice is redundant by its copy, so `[0, 1] = {x ≤ 1, x ≤ 1, -x ≤ 0}` passes against
`{x ≥ 0} = {-x ≤ 0}`: both copies of `x ≤ 1` are redundant, `-x ≤ 0` is matched. [1, Alg. 1]
requires a minimal representation, which rules this out; CORA's `aux_isequal_nondeg` in
`@polytope/isequal.m` runs the same test on the constraints as given (see `FINDINGS.md`).

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isequalNondeg_duplicate_counterexample :
    ∃ (A₁ : Mat ℝ 3 1) (b₁ : Vec ℝ 3) (A₂ : Mat ℝ 1 1) (b₂ : Vec ℝ 1),
      HPolytope.isequalNondeg A₁ b₁ A₂ b₂ = true ∧
        (HPolytope.ineqs A₁ b₁).construct ≠ (HPolytope.ineqs A₂ b₂).construct := by -- --- PROOF ---
  let A₁ : Mat ℝ 3 1 := !![1; 1; -1]
  let A₂ : Mat ℝ 1 1 := !![-1]
  -- every row is a unit vector, so line 1 changes nothing
  have hn₁ : ∀ j, ‖A₁ j‖₂ = 1 := fun j => by fin_cases j <;> simp [A₁, norm₂]
  have hn₂ : ∀ k, ‖A₂ k‖₂ = 1 := fun k => by fin_cases k; simp [A₂, norm₂]
  have hN₁ : (Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j) = A₁ := by
    ext j i
    simp [hn₁]
  have hN₂ : (Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k) = A₂ := by
    ext k i
    simp [hn₂]
  refine ⟨A₁, ![1, 1, 0], A₂, ![0], ?_, fun he => ?_⟩
  · unfold HPolytope.isequalNondeg
    simp only [hN₁, hN₂, Bool.if_false_right, Bool.and_true, decide_eq_true_eq]
    refine ⟨fun j => ?_, fun k => Or.inl ⟨2, ?_⟩⟩
    · fin_cases j
      -- each copy of `x ≤ 1` is redundant by the other
      · refine Or.inr (supportFunc_le_coe_iff.mpr fun x hx => ?_)
        have := HPolytope.mem_ineqs_iff.mp hx 0
        exact this
      · refine Or.inr (supportFunc_le_coe_iff.mpr fun x hx => ?_)
        have := HPolytope.mem_ineqs_iff.mp hx 0
        exact this
      · exact Or.inl ⟨0, by ext i; fin_cases i; rfl, rfl⟩
    · fin_cases k
      exact ⟨by ext i; fin_cases i; rfl, rfl⟩
  -- `2` is in `[0, ∞)` and not in `[0, 1]`
  · have h2 : (![2] : Vec ℝ 1) ∈ (HPolytope.ineqs A₂ ![0]).construct :=
      HPolytope.mem_ineqs_iff.mpr fun k => by fin_cases k; simp [A₂, mulVec, dotProduct]
    rw [← he] at h2
    have := HPolytope.mem_ineqs_iff.mp h2 0
    simp [A₁, mulVec, dotProduct] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
