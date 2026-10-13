module

public import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaIntervalZeroRowCora
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's `polytope/representsa_(P, 'interval')` converts an empty polytope to a nonempty box

`aux_isInterval` skips every all-zero row (`if ~any(constraint) continue`, l. 259), including the
infeasible `0 x ≤ b` with `b < 0`. For `P = {-1 ≤ x ≤ 1, -1 ≤ y ≤ 1, 0 ≤ -1}` in `ℝ²` (an
H-representation, whose emptiness `representsa_emptyObject` does not see: it has rows), no row
is flagged for the redundancy walk, and CORA returns `res = true` with `I = [-1,1]²`, though
`P` is empty; the right interval is `interval.empty(2)`. (For `n = 1` the box is `(-Inf,Inf)`.)
A wrong output of the conversion, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The box `[-1,1]²` with the infeasible row `0 x ≤ -1` added. -/
def HPolytope.aux_boxZeroRow : HPolytope (Fin 2 → ℝ) where
  m := 5
  A := let p0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    let p1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
    ![p0, -p0, p1, -p1, 0]
  b := ![1, 1, 1, 1, -1]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.aux_boxZeroRow_construct :
    HPolytope.aux_boxZeroRow.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h, -⟩
  have h4 := h (4 : Fin 5)
  simp [HPolytope.aux_boxZeroRow] at h4
  norm_num at h4

-- a nonnegative offset gives an update `≥ 0` for `ub`
theorem HPolytope.aux_rowUpper_nonneg (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (j : Fin 2)
    (hc : 0 ≤ c) : 0 ≤ HPolytope.rowUpperCora f c j := by
  unfold HPolytope.rowUpperCora
  split_ifs
  · exact EReal.coe_nonneg.2 (div_nonneg hc (abs_nonneg _))
  · exact le_top

-- a nonnegative offset gives an update `≤ 0` for `lb`
theorem HPolytope.aux_rowLower_nonpos (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (j : Fin 2)
    (hc : 0 ≤ c) : HPolytope.rowLowerCora f c j ≤ 0 := by
  unfold HPolytope.rowLowerCora
  split_ifs
  · exact EReal.coe_nonpos.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg _))
  · exact bot_le

-- the zero row changes neither bound
theorem HPolytope.aux_rowUpper_zero (c : ℝ) (j : Fin 2) :
    HPolytope.rowUpperCora (0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) c j = ⊤ := by
  unfold HPolytope.rowUpperCora
  rw [if_neg]
  simp

theorem HPolytope.aux_rowLower_zero (c : ℝ) (j : Fin 2) :
    HPolytope.rowLowerCora (0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) c j = ⊥ := by
  unfold HPolytope.rowLowerCora
  rw [if_neg]
  simp

/-- A row with one possibly nonzero coordinate `k` has no two nonzero entries. -/
theorem HPolytope.aux_not_flagged (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (k : Fin 2)
    (hf : ∀ i, f (Pi.single i 1) ≠ 0 → i = k) :
    ¬ ∃ i j, i ≠ j ∧ f (Pi.single i 1) ≠ 0 ∧ f (Pi.single j 1) ≠ 0 := by
  rintro ⟨i, j, hij, hi, hj⟩
  exact hij ((hf i hi).trans (hf j hj).symm)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P` is empty, yet whatever the redundancy walk would return, CORA's `I` is a box containing
the origin. -/
theorem HPolytope.representsa_interval_zeroRow_cora_counterexample
    (rest : (Fin 2 → EReal) × (Fin 2 → EReal)) :
    HPolytope.aux_boxZeroRow.construct = ∅ ∧
      ∀ j, (HPolytope.aux_boxZeroRow.representsaIntervalZeroRowCora rest).1 j ≤ 0 ∧
        0 ≤
          (HPolytope.aux_boxZeroRow.representsaIntervalZeroRowCora rest).2 j := by -- --- PROOF ---
  -- the polytope is empty; no row is flagged, so `(lb, ub)` is returned
  refine ⟨HPolytope.aux_boxZeroRow_construct, ?_⟩
  have hA : ∀ i, ¬ ∃ a b, a ≠ b ∧ (HPolytope.aux_boxZeroRow.A i) (Pi.single a 1) ≠ 0 ∧
      (HPolytope.aux_boxZeroRow.A i) (Pi.single b 1) ≠ 0 := by
    -- each of the five rows has at most one nonzero coordinate
    intro i
    fin_cases i
    · exact HPolytope.aux_not_flagged _ 0 fun i hi => by
        by_contra h; apply hi; simp [HPolytope.aux_boxZeroRow, Ne.symm h]
    · exact HPolytope.aux_not_flagged _ 0 fun i hi => by
        by_contra h; apply hi; simp [HPolytope.aux_boxZeroRow, Ne.symm h]
    · exact HPolytope.aux_not_flagged _ 1 fun i hi => by
        by_contra h; apply hi; simp [HPolytope.aux_boxZeroRow, Ne.symm h]
    · exact HPolytope.aux_not_flagged _ 1 fun i hi => by
        by_contra h; apply hi; simp [HPolytope.aux_boxZeroRow, Ne.symm h]
    · exact HPolytope.aux_not_flagged _ 0 fun i hi => by
        exfalso; apply hi; simp [HPolytope.aux_boxZeroRow]
  -- the equality part has no rows
  have hnf : ¬ ((∃ i : Fin HPolytope.aux_boxZeroRow.m, ∃ a b, a ≠ b ∧
        (HPolytope.aux_boxZeroRow.A i) (Pi.single a 1) ≠ 0 ∧
        (HPolytope.aux_boxZeroRow.A i) (Pi.single b 1) ≠ 0) ∨
      (∃ i : Fin HPolytope.aux_boxZeroRow.me, ∃ a b, a ≠ b ∧
        (HPolytope.aux_boxZeroRow.Ae i) (Pi.single a 1) ≠ 0 ∧
        (HPolytope.aux_boxZeroRow.Ae i) (Pi.single b 1) ≠ 0)) := by
    rintro (⟨i, hi⟩ | ⟨i, -⟩)
    · exact hA i hi
    · exact absurd i.2 (Nat.not_lt_zero _)
  intro j
  unfold HPolytope.representsaIntervalZeroRowCora
  simp only [hnf, if_false]
  constructor
  -- every lower update `-c/|a|` has `c ≥ 0`, so is `≤ 0`; the zero row gives `-Inf`
  · refine sup_le (sup_le (iSup_le fun i => ?_) (iSup_le fun i => ?_)) (iSup_le fun i => ?_)
    rotate_left
    · exact absurd i.2 (Nat.not_lt_zero _)
    · exact absurd i.2 (Nat.not_lt_zero _)
    · fin_cases i
      · exact HPolytope.aux_rowLower_nonpos _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowLower_nonpos _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowLower_nonpos _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowLower_nonpos _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · simp [HPolytope.aux_boxZeroRow, HPolytope.aux_rowLower_zero]
  -- every upper update `c/|a|` has `c ≥ 0`, so is `≥ 0`; the zero row gives `Inf`
  · refine le_inf (le_inf (le_iInf fun i => ?_) (le_iInf fun i => ?_)) (le_iInf fun i => ?_)
    rotate_left
    · exact absurd i.2 (Nat.not_lt_zero _)
    · exact absurd i.2 (Nat.not_lt_zero _)
    · fin_cases i
      · exact HPolytope.aux_rowUpper_nonneg _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowUpper_nonneg _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowUpper_nonneg _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · exact HPolytope.aux_rowUpper_nonneg _ _ _ (by simp [HPolytope.aux_boxZeroRow])
      · simp [HPolytope.aux_boxZeroRow, HPolytope.aux_rowUpper_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
