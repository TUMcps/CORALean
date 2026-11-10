module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

/-!
# `HPolytope.mldivideCora`: `mldivide` as CORA's code computes it

`@polytope/mldivide.m` returns `P1 \ P2` as a union of polytopes, but line 26 reads
`P2 = compact_(P1,'all',1e-9);` where it means `compact_(P2, ...)`, so after the two early
returns (`P1` empty, `P2` empty) both operands are `P1`. For a full-dimensional `P1` the loop of
l. 41-48 builds cells `[-a_i; P1_A(1:i-1); P1_A]` that contain the halfspace `a_i x ≤ b_i` and its
flip, so none is full-dimensional, none replaces the initial `P_out = polytope(zeros(0,n),[])`, and
that polytope, the whole space, is returned. The other branches (a lower-dimensional `P1`) are the
parameter `rest`. `compact_` does not change the set. The difference algorithm is not formalized;
this is the set the code denotes. Run in MATLAB R2024b with CORA v2026.1.0 (904a444), see
`experiments/cora-bugs/results.tsv`.

# CORA's `polytope/mldivide` returns the whole space

For `P1 = [0, 2]` and `P2 = [1, 3]` the difference `P1 \ P2` is `[0, 1)`, and CORA's result is the
whole line (`A = zeros(0,1)`). A first reading of the code took the result for the difference of
`P1` with itself, which is empty; the run showed the initial value of `P_out` instead.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's result is not `P1 \ P2` for `P1 = [0, 2]`, `P2 = [1, 3]`
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   10-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- The set CORA's `mldivide` returns: the two early returns, then, for a full-dimensional `P1`, the
whole space (`P_out` is never replaced); `rest` is the value of the other branches. -/
noncomputable def HPolytope.mldivideCora (P₁ P₂ : HPolytope (Vec ℝ n)) (rest : Set (Vec ℝ n)) :
    Set (Vec ℝ n) :=
  if P₁.toSet = ∅ then ∅
  else if P₂.toSet = ∅ then P₁.toSet
  else if (interior P₁.toSet).Nonempty then Set.univ
  else rest

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The interval `[lo, hi]` of `ℝ¹` by two halfspaces. -/
private def HPolytope.aux_interval1 (lo hi : ℝ) : HPolytope (Vec ℝ 1) where
  m := 2
  A := ![(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ), -(LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ)]
  b := ![hi, -lo]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's result is not `P1 \ P2` for `P1 = [0, 2]`, `P2 = [1, 3]`. -/
theorem HPolytope.mldivide_cora_counterexample : -- --- CONCL ---
    ∃ P₁ P₂ : HPolytope (Vec ℝ 1),
      ∀ rest, P₁.mldivideCora P₂ rest ≠ P₁.toSet \ P₂.toSet := by -- --- PROOF ---
  -- membership in the interval `[lo, hi]`
  have mem : ∀ (lo hi : ℝ) (x : Vec ℝ 1),
      x ∈ (HPolytope.aux_interval1 lo hi).toSet ↔ lo ≤ x 0 ∧ x 0 ≤ hi := by
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
  refine ⟨HPolytope.aux_interval1 0 2, HPolytope.aux_interval1 1 3, fun rest h => ?_⟩
  -- neither operand is empty
  have hne1 : (HPolytope.aux_interval1 0 2).toSet ≠ ∅ := fun he =>
    Set.eq_empty_iff_forall_notMem.mp he (fun _ => 1)
      ((mem _ _ _).mpr ⟨by show (0 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 2; norm_num⟩)
  have hne2 : (HPolytope.aux_interval1 1 3).toSet ≠ ∅ := fun he =>
    Set.eq_empty_iff_forall_notMem.mp he (fun _ => 2)
      ((mem _ _ _).mpr ⟨by show (1 : ℝ) ≤ 2; norm_num, by show (2 : ℝ) ≤ 3; norm_num⟩)
  -- `P₁` has an interior point `1`: the open slab `0 < x < 2` lies in it
  have hint : (interior (HPolytope.aux_interval1 0 2).toSet).Nonempty := by
    have hsub : {x : Vec ℝ 1 | 0 < x 0 ∧ x 0 < 2} ⊆ (HPolytope.aux_interval1 0 2).toSet :=
      fun x hx => (mem _ _ _).mpr ⟨hx.1.le, hx.2.le⟩
    have hopen : IsOpen {x : Vec ℝ 1 | 0 < x 0 ∧ x 0 < 2} :=
      (isOpen_lt continuous_const (continuous_apply 0)).inter
        (isOpen_lt (continuous_apply 0) continuous_const)
    exact ⟨fun _ => 1, interior_maximal hsub hopen (by show (0 : ℝ) < 1 ∧ (1 : ℝ) < 2; norm_num)⟩
  -- so CORA returns the whole space, which contains `5`, a point outside `P₁`
  have h5 : (fun _ => 5 : Vec ℝ 1) ∈ HPolytope.mldivideCora (HPolytope.aux_interval1 0 2)
      (HPolytope.aux_interval1 1 3) rest := by
    unfold HPolytope.mldivideCora
    rw [if_neg hne1, if_neg hne2, if_pos hint]
    exact Set.mem_univ _
  rw [h] at h5
  have := ((mem _ _ _).mp h5.1).2
  change (5 : ℝ) ≤ 2 at this
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
