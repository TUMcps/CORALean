module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.mldivideCora`: `mldivide` as CORA's code computes it

`@polytope/mldivide.m` returns `P1 \ P2` as a union of polytopes, but line 26 reads
`P2 = compact_(P1,'all',1e-9);` where it means `compact_(P2, ...)`, so after the two early
returns (`P1` empty, `P2` empty) both operands are `P1`, and the rest of the code, which computes
the difference of its two arguments, returns `P1 \ P1`. `compact_` does not change the set.
The difference algorithm is not formalized; this is the set it denotes at `(P1, P1)`.
Read from the source, not run.

# CORA's `polytope/mldivide` computes `P1 \ P1`

For `P1 = [0, 2]` and `P2 = [1, 3]` the difference `P1 \ P2` contains `0`, and CORA's result,
the difference of `P1` with itself, is empty. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's result is not `P1 \ P2` for `P1 = [0, 2]`, `P2 = [1, 3]`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The set CORA's `mldivide` returns: the two early returns, then `P1 \ P1`. -/
noncomputable def HPolytope.mldivideCora (P₁ P₂ : HPolytope (Vec ℝ n)) : Set (Vec ℝ n) :=
  open Classical in
  if P₁.construct = ∅ then ∅
  else if P₂.construct = ∅ then P₁.construct
  else P₁.construct \ P₁.construct

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The interval `[lo, hi]` of `ℝ¹` by two halfspaces. -/
def HPolytope.aux_interval1 (lo hi : ℝ) : HPolytope (Vec ℝ 1) where
  m := 2
  A := ![(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ), -(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ)]
  b := ![hi, -lo]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's result is not `P1 \ P2` for `P1 = [0, 2]`, `P2 = [1, 3]`. -/
theorem HPolytope.mldivide_cora_counterexample :
    ∃ P₁ P₂ : HPolytope (Vec ℝ 1),
      P₁.mldivideCora P₂ ≠ P₁.construct \ P₂.construct := by -- --- PROOF ---
  have mem : ∀ (lo hi : ℝ) (x : Vec ℝ 1),
      x ∈ (HPolytope.aux_interval1 lo hi).construct ↔ lo ≤ x 0 ∧ x 0 ≤ hi := by
    intro lo hi x
    constructor
    · rintro ⟨h, -⟩
      have h0 := h (0 : Fin 2)
      have h1 := h (1 : Fin 2)
      simp [HPolytope.aux_interval1] at h0 h1
      exact ⟨by linarith, h0⟩
    · rintro ⟨h0, h1⟩
      refine ⟨fun i => ?_, fun i => i.elim0⟩
      fin_cases i
      · simpa [HPolytope.aux_interval1] using h1
      · simpa [HPolytope.aux_interval1] using h0
  refine ⟨HPolytope.aux_interval1 0 2, HPolytope.aux_interval1 1 3, fun h => ?_⟩
  -- `0` is in `P₁ \ P₂`, and neither operand is empty, so CORA's result is `P₁ \ P₁`
  have h0 : (0 : Vec ℝ 1) ∈ (HPolytope.aux_interval1 0 2).construct
      \ (HPolytope.aux_interval1 1 3).construct :=
    ⟨(mem _ _ _).mpr ⟨le_rfl, by simp⟩, fun hm => by
      have := ((mem _ _ _).mp hm).1
      simp at this; linarith⟩
  have hne1 : (HPolytope.aux_interval1 0 2).construct ≠ ∅ := fun he => by
    have := h0.1; rw [he] at this; exact this
  have hne2 : (HPolytope.aux_interval1 1 3).construct ≠ ∅ := fun he =>
    Set.eq_empty_iff_forall_notMem.mp he (fun _ => 2)
      ((mem _ _ _).mpr ⟨by show (1 : ℝ) ≤ 2; norm_num, by show (2 : ℝ) ≤ 3; norm_num⟩)
  rw [← h] at h0
  unfold HPolytope.mldivideCora at h0
  rw [if_neg hne1, if_neg hne2] at h0
  exact h0.2 h0.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
