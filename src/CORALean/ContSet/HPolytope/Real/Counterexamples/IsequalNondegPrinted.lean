module

public import CORALean.ContSet.HPolytope.Real.Theorems.InteriorNonemptyIffChebyshev
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.Global.DropIdx
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `[1, Alg. 1]` as printed accepts `[0, 1] = [0, 2]`

Line 4 prints the failure condition as `ρ(⟨A₁*, b₁*⟩, A₁(j,·)ᵀ) = b₁(j)`, which says the row is
redundant — impossible in the minimal representation the algorithm requires. So the printed test
never returns `⊥`: `[0, 1] = {x ≤ 1, -x ≤ 0}` and `[0, 2] = {x ≤ 2, -x ≤ 0}` are non-degenerate,
minimal and normalized, the rows `x ≤ 1` and `x ≤ 2` find no partner, and neither satisfies the
printed condition, the support function without them being `+∞`. `isequalNondeg` reads line 4 as
the text describes it.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Alg. 1]` as printed accepts `[0, 1] = [0, 2]`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isequalNondeg_printed_counterexample : -- --- CONCL ---
    ∃ (A₁ : Mat ℝ 2 1) (b₁ : Vec ℝ 2) (A₂ : Mat ℝ 2 1) (b₂ : Vec ℝ 2),
      (∀ j, ‖A₁ j‖₂ = 1) ∧ (∀ k, ‖A₂ k‖₂ = 1) ∧
      (interior (HPolytope.ineqs A₁ b₁).construct).Nonempty ∧
      (interior (HPolytope.ineqs A₂ b₂).construct).Nonempty ∧
      (∀ j, (HPolytope.ineqs A₁ b₁).construct ≠
        (HPolytope.ineqs (A₁.submatrix (dropIdx j) id) fun i => b₁ (dropIdx j i)).construct) ∧
      (∀ k, (HPolytope.ineqs A₂ b₂).construct ≠
        (HPolytope.ineqs (A₂.submatrix (dropIdx k) id) fun i => b₂ (dropIdx k i)).construct) ∧
      (∀ j, (∃ k, A₁ j = A₂ k ∧ b₁ j = b₂ k) ∨
        supportFunc
          (HPolytope.ineqs (A₁.submatrix (dropIdx j) id) fun i => b₁ (dropIdx j i)).construct
          (HPolytope.rowLin A₁ j) ≠ (b₁ j : EReal)) ∧
      (∀ k, (∃ j, A₂ k = A₁ j ∧ b₂ k = b₁ j) ∨
        supportFunc
          (HPolytope.ineqs (A₂.submatrix (dropIdx k) id) fun i => b₂ (dropIdx k i)).construct
          (HPolytope.rowLin A₂ k) ≠ (b₂ k : EReal)) ∧
      (HPolytope.ineqs A₁ b₁).construct ≠ (HPolytope.ineqs A₂ b₂).construct := by -- --- PROOF ---
  let A : Mat ℝ 2 1 := !![1; -1]
  have hA : ∀ x : Vec ℝ 1, A *ᵥ x = ![x 0, -x 0] := fun x => by
    funext i
    fin_cases i <;> simp [A, mulVec, dotProduct]
  have hn : ∀ j, ‖A j‖₂ = 1 := by
    intro j
    fin_cases j <;> simp [A, norm₂]
  have hd0 : dropIdx (0 : Fin 2) 0 = 1 := rfl
  have hd1 : dropIdx (1 : Fin 2) 0 = 0 := rfl
  -- membership in `[0, c]` and in its two relaxations
  have hmem : ∀ (c : ℝ) (x : Vec ℝ 1), x ∈ (HPolytope.ineqs A ![c, 0]).construct ↔
      x 0 ≤ c ∧ -x 0 ≤ 0 := fun c x => by
    rw [HPolytope.mem_ineqs_iff, hA]
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa using h0
      · simp
        linarith
  -- without `x ≤ c`, only `-x ≤ 0` is left
  have hdrop0 : ∀ (c : ℝ) (x : Vec ℝ 1), x ∈ (HPolytope.ineqs (A.submatrix (dropIdx 0) id)
      fun i => (![c, 0] : Vec ℝ 2) (dropIdx 0 i)).construct ↔ -x 0 ≤ 0 := fun c x => by
    rw [HPolytope.mem_ineqs_iff]
    constructor
    · intro h
      have := h 0
      change (A *ᵥ x) (dropIdx 0 0) ≤ (![c, 0] : Vec ℝ 2) (dropIdx 0 0) at this
      rw [hd0, hA] at this
      simpa using this
    · intro h i
      obtain rfl : i = 0 := Fin.ext (by omega)
      change (A *ᵥ x) (dropIdx 0 0) ≤ (![c, 0] : Vec ℝ 2) (dropIdx 0 0)
      rw [hd0, hA]
      simpa using h
  -- without `-x ≤ 0`, only `x ≤ c` is left
  have hdrop1 : ∀ (c : ℝ) (x : Vec ℝ 1), x ∈ (HPolytope.ineqs (A.submatrix (dropIdx 1) id)
      fun i => (![c, 0] : Vec ℝ 2) (dropIdx 1 i)).construct ↔ x 0 ≤ c := fun c x => by
    rw [HPolytope.mem_ineqs_iff]
    constructor
    · intro h
      have := h 0
      change (A *ᵥ x) (dropIdx 1 0) ≤ (![c, 0] : Vec ℝ 2) (dropIdx 1 0) at this
      rw [hd1, hA] at this
      simpa using this
    · intro h i
      obtain rfl : i = 0 := Fin.ext (by omega)
      change (A *ᵥ x) (dropIdx 1 0) ≤ (![c, 0] : Vec ℝ 2) (dropIdx 1 0)
      rw [hd1, hA]
      simpa using h
  -- non-degenerate: a ball of radius `1/2` fits around `c/2`
  have hint : ∀ c : ℝ, 1 ≤ c → (interior (HPolytope.ineqs A ![c, 0]).construct).Nonempty :=
    fun c hc => (HPolytope.ineqs_interior_nonempty_iff _ _).mpr ⟨![1 / 2], 1 / 2, by norm_num,
      fun j => by
        rw [hn j, hA]
        fin_cases j
        · simp
          linarith
        · simp⟩
  -- minimal: each row cuts something off
  have hmin : ∀ c : ℝ, 0 < c → ∀ j, (HPolytope.ineqs A ![c, 0]).construct ≠
      (HPolytope.ineqs (A.submatrix (dropIdx j) id)
        fun i => (![c, 0] : Vec ℝ 2) (dropIdx j i)).construct := by
    intro c hc
    refine Fin.forall_fin_two.mpr ⟨fun he => ?_, fun he => ?_⟩
    · have h := (hdrop0 c ![c + 1]).mpr (by simp only [Matrix.cons_val_zero]; linarith)
      rw [← he, hmem] at h
      simp only [Matrix.cons_val_zero] at h
      linarith [h.1]
    · have h := (hdrop1 c ![-1]).mpr (by simp only [Matrix.cons_val_zero]; linarith)
      rw [← he, hmem] at h
      simp only [Matrix.cons_val_zero] at h
      linarith [h.2]
  -- the row `x ≤ c` is not redundant in the printed sense: without it, `x` is unbounded
  have hρ : ∀ c : ℝ, supportFunc (HPolytope.ineqs (A.submatrix (dropIdx 0) id)
      fun i => (![c, 0] : Vec ℝ 2) (dropIdx 0 i)).construct (HPolytope.rowLin A 0) ≠
        ((![c, 0] : Vec ℝ 2) 0 : EReal) := by
    intro c h
    have hle := supportFunc_le_coe_iff.mp h.le ![|c| + 1]
      ((hdrop0 c _).mpr (by simp only [Matrix.cons_val_zero]; linarith [abs_nonneg c]))
    have : HPolytope.rowLin A 0 ![|c| + 1] = |c| + 1 := by
      show (A *ᵥ ![|c| + 1]) 0 = _
      rw [hA]
      simp
    rw [this] at hle
    simp at hle
    linarith [le_abs_self c]
  -- `[0, 1]` against `[0, 2]`
  refine ⟨A, ![1, 0], A, ![2, 0], hn, hn, hint 1 le_rfl, hint 2 (by norm_num),
    hmin 1 one_pos, hmin 2 two_pos, fun j => ?_, fun k => ?_, fun he => ?_⟩
  · revert j
    exact Fin.forall_fin_two.mpr ⟨Or.inr (hρ 1), Or.inl ⟨1, rfl, rfl⟩⟩
  · revert k
    exact Fin.forall_fin_two.mpr ⟨Or.inr (hρ 2), Or.inl ⟨1, rfl, rfl⟩⟩
  · have h := (hmem 2 ![2]).mpr (by simp)
    rw [← he, hmem] at h
    norm_num at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
