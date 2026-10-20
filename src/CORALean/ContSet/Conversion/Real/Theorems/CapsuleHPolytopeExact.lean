module

public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm
public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.GramSchmidtVecColZero
public import CORALean.ContSet.Conversion.Real.Theorems.GramSchmidtVecOrthogonal
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalHPolytopeExact
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet
public import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact

@[expose] public section

/-!
# CORA's exact branches of `polytope(C)` are exact

The capsule and its polytope are the same set where CORA's `@capsule/polytope.m` returns before
reaching `'outer'`: an empty capsule, `n = 1` (`aux_1D`), a point, and a segment
(`aux_exactLineConversion`). At `n = 1` a point of the capsule is `d = t a + e` with `|t| ≤ 1`,
`|e| ≤ r`, which is `|d| ≤ |a| + r`. On the segment the basis does the work: `gramSchmidt(g)` is
orthogonal (`gramSchmidtVec_transpose_mul_self`) with first column `g / ‖g‖₂`, so `x - c` with no
component along the other columns is its component along `g / ‖g‖₂`, a multiple `t g`, and the
two inequality rows say `|t| ≤ 1`.

## Inputs
* `n` – dimension
* `C` – capsule

## Hypotheses
* `h` – dimension at most one or radius not positive

## Conclusion
* halfspace polytope equals the capsule
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_norm₂_nonpos_iff {n : ℕ} {v : Vec ℝ n} : ‖v‖₂ ≤ 0 ↔ v = 0 := by
  rw [← norm_toEuclidean, norm_le_zero_iff, map_eq_zero_iff _ toEuclidean.injective]

/-- At radius `0` a capsule is its segment. -/
private theorem aux_mem_of_r_eq_zero {n : ℕ} {C : Capsule n} (hr : C.r = 0) (x : Vec ℝ n) :
    x ∈ C.construct ↔ ∃ t ∈ Set.Icc (-1 : ℝ) 1, x - C.c = t • C.g := by
  rw [Capsule.mem_construct_iff_norm₂, hr]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [aux_norm₂_nonpos_iff, sub_eq_zero]

/-- A displacement `d` is `t a` plus at most `r`, `|t| ≤ 1`, exactly when `|d| ≤ |a| + r`. -/
private theorem aux_exists_abs_sub_le_iff {d a r : ℝ} (hr : 0 ≤ r) : -- --- CONCL ---
    (∃ t ∈ Set.Icc (-1 : ℝ) 1, |d - t * a| ≤ r) ↔ |d| ≤ |a| + r := by -- --- PROOF ---
  constructor
  · rintro ⟨t, ht, hle⟩
    have hta : |t * a| ≤ |a| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg a) (abs_le.mpr (Set.mem_Icc.mp ht))
    calc |d| = |(d - t * a) + t * a| := by ring_nf
      _ ≤ |d - t * a| + |t * a| := abs_add_le _ _
      _ ≤ |a| + r := by linarith
  intro h
  by_cases hda : |d| ≤ |a|
  · -- inside the segment's reach: hit `d` exactly
    by_cases ha : a = 0
    · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [ha, abs_zero] at hda
      rw [abs_nonpos_iff.mp hda, zero_mul, sub_zero, abs_zero]
      exact hr
    · refine ⟨d / a, ?_, ?_⟩
      · have h1 : |d / a| ≤ 1 := by
          rw [abs_div]
          exact div_le_one_of_le₀ hda (abs_nonneg a)
        exact abs_le.mp h1
      · rw [div_mul_cancel₀ d ha, sub_self, abs_zero]
        exact hr
  -- beyond it: the segment's end on `d`'s side, the rest within `r`
  push Not at hda
  rcases le_total 0 d with hd | hd <;> rcases le_total 0 a with ha | ha
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [abs_of_nonneg hd, abs_of_nonneg ha] at h hda
    rw [one_mul, abs_le]
    constructor <;> linarith
  · refine ⟨-1, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [abs_of_nonneg hd, abs_of_nonpos ha] at h hda
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨-1, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [abs_of_nonpos hd, abs_of_nonneg ha] at h hda
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [abs_of_nonpos hd, abs_of_nonpos ha] at h hda
    rw [one_mul, abs_le]
    constructor <;> linarith

/-- `aux_1D` is exact: the capsule on the line is the interval `c ± (|g| + r)`. -/
private theorem aux_hPolytope_1D (C : Capsule (0 + 1)) (hr : 0 ≤ C.r) : -- --- CONCL ---
    C.interval.hPolytope.construct = C.construct := by -- --- PROOF ---
  rw [Interval.hPolytope_exact]
  ext x
  rw [Capsule.mem_construct_iff_norm₂]
  -- one coordinate: `‖v‖₂ = |v 0|`
  have h1 : ∀ v : Vec ℝ (0 + 1), ‖v‖₂ = |v 0| := fun v => by
    simp [norm₂, Real.sqrt_sq_eq_abs]
  simp only [h1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [aux_exists_abs_sub_le_iff hr, abs_le]
  simp only [Interval.construct, Capsule.interval, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨h₁, h₂⟩ : C.c 0 - (|C.g 0| + C.r) ≤ x 0 ∧ x 0 ≤ C.c 0 + (|C.g 0| + C.r) := hx 0
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩ i
    fin_cases i
    show C.c 0 - (|C.g 0| + C.r) ≤ x 0 ∧ x 0 ≤ C.c 0 + (|C.g 0| + C.r)
    constructor <;> linarith

/-- CORA's `aux_exactLineConversion` is exact at `r = 0`, `g ≠ 0`. -/
private theorem aux_hPolytope_line (C : Capsule (m + 1)) (hr : C.r = 0)
    (hg : C.g ≠ 0) : -- --- CONCL ---
    C.hPolytopeOfLine.construct = C.construct := by -- --- PROOF ---
  set Q := gramSchmidtVec C.g with hQdef
  set q : Fin (m + 1) → Vec ℝ (m + 1) := Qᵀ with hqdef
  -- the columns are orthonormal, span, and the first is `g / ‖g‖₂`
  have hon : ∀ i j, q i ⬝ᵥ q j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun (gramSchmidtVec_transpose_mul_self hg) i) j
    rw [mul_apply, one_apply] at this
    rw [← this]
    rfl
  -- `Q Qᵀ = 1`: every vector is the sum of its components along the columns
  have hspan : ∀ y : Vec ℝ (m + 1), y = ∑ j, (q j ⬝ᵥ y) • q j := fun y => by
    have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp (gramSchmidtVec_transpose_mul_self hg)
    funext i
    have := congrFun (congrFun hQQ i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc y i = ∑ r, (1 : Mat ℝ (m + 1) (m + 1)) i r * y r := by
          simp [one_apply]
      _ = ∑ r, (∑ j, Q i j * Q r j) * y r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← this r, mul_apply]
          rfl
      _ = ∑ j, (q j ⬝ᵥ y) * q j i := by
          simp only [Finset.sum_mul, dotProduct, hqdef, transpose_apply]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
          ring
  -- `g` is its length times the first column, so the others are orthogonal to it
  have hq0 : q 0 = (‖C.g‖₂)⁻¹ • C.g := gramSchmidtVec_col_zero C.g
  have hpos : 0 < ‖C.g‖₂ := lt_of_le_of_ne (norm₂_nonneg _)
    (fun h => hg (aux_norm₂_nonpos_iff.mp h.symm.le))
  have hgq : C.g = ‖C.g‖₂ • q 0 := by
    rw [hq0, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hgg : q 0 ⬝ᵥ C.g = ‖C.g‖₂ := by
    rw [hq0, smul_dotProduct, dotProduct_self, smul_eq_mul, sq, ← mul_assoc,
      inv_mul_cancel₀ hpos.ne', one_mul]
  have hgl : ∀ l : Fin m, q l.succ ⬝ᵥ C.g = 0 := fun l => by
    rw [hgq, dotProduct_smul, hon, if_neg (Fin.succ_ne_zero l), smul_zero]
  -- membership in the translated rows, read at `y = x - c`
  ext x
  rw [aux_mem_of_r_eq_zero hr, Capsule.hPolytopeOfLine, ← HPolytope.translate_exact]
  simp only [← hQdef, ← hqdef]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← HPolytope.intersection_exact] at hy
    obtain ⟨hin, heq⟩ := hy
    rw [HPolytope.mem_ineqs_iff] at hin
    rw [HPolytope.mem_eqs_iff] at heq
    have hle := hin 0
    have hge := hin 1
    simp only [mulVec, cons_val_zero, cons_val_one, neg_dotProduct] at hle hge
    -- `y` has no component off the first column, so it is `(q₀ ⬝ y) / ‖g‖₂` times `g`
    have hzero : ∀ l : Fin m, q l.succ ⬝ᵥ y = 0 := fun l => by
      simpa [mulVec] using heq l
    refine ⟨(q 0 ⬝ᵥ y) / ‖C.g‖₂, ?_, ?_⟩
    · have : |(q 0 ⬝ᵥ y) / ‖C.g‖₂| ≤ 1 := by
        rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
        constructor <;> linarith
      exact abs_le.mp this
    · rw [add_sub_cancel_left]
      conv_lhs => rw [hspan y, Fin.sum_univ_succ]
      simp only [hzero, zero_smul, Finset.sum_const_zero, add_zero]
      rw [hq0, smul_smul, div_eq_mul_inv]
  -- back: a segment point `c + t g` meets both rows and every equality
  · rintro ⟨t, ht, hx⟩
    refine ⟨x - C.c, ?_, add_sub_cancel C.c x⟩
    rw [← HPolytope.intersection_exact]
    refine ⟨HPolytope.mem_ineqs_iff.mpr fun i => ?_, HPolytope.mem_eqs_iff.mpr fun l => ?_⟩
    · have hval : q 0 ⬝ᵥ (x - C.c) = t * ‖C.g‖₂ := by
        rw [hx, dotProduct_smul, hgg, smul_eq_mul]
      have habs : |t * ‖C.g‖₂| ≤ ‖C.g‖₂ := by
        rw [abs_mul, abs_of_pos hpos]
        exact mul_le_of_le_one_left hpos.le (abs_le.mpr (Set.mem_Icc.mp ht))
      fin_cases i <;> simp only [mulVec, cons_val_zero, cons_val_one, neg_dotProduct,
        Fin.zero_eta, Fin.mk_one, hval] <;> linarith [abs_le.mp habs]
    · show q l.succ ⬝ᵥ (x - C.c) = 0
      rw [hx, dotProduct_smul, hgl, smul_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where CORA's `polytope(C)` returns before `'outer'` — `n ≤ 1`, or no radius — it is exact. -/
theorem Capsule.hPolytope_exact {n : ℕ} (C : Capsule n) (h : n ≤ 1 ∨ C.r ≤ 0) : -- --- CONCL ---
    C.hPolytope.construct = C.construct := by -- --- PROOF ---
  cases n with
  | zero =>
    show (if C.r < 0 then _ else _ : HPolytope (Vec ℝ 0)).construct = _
    split_ifs with hr
    · rw [HPolytope.construct_emptySet, Capsule.construct_eq_empty hr]
    · -- `Vec ℝ 0` is a single point, and a radius `≥ 0` keeps it
      ext x
      rw [HPolytope.mem_ofPoint_iff, Capsule.mem_construct_iff_norm₂]
      refine ⟨fun _ => ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩, fun _ => funext fun i => i.elim0⟩
      rw [show (x - C.c) - (0 : ℝ) • C.g = 0 from funext fun i => i.elim0, norm₂_zero]
      exact not_lt.mp hr
  | succ m =>
    show (if C.r < 0 then _ else if m = 0 then _ else if C.g = 0 ∧ C.r = 0 then _
      else if C.r = 0 then _ else _ : HPolytope (Vec ℝ (m + 1))).construct = _
    split_ifs with hr hm hpt hline
    · rw [HPolytope.construct_emptySet, Capsule.construct_eq_empty hr]
    · subst hm
      exact aux_hPolytope_1D C (not_lt.mp hr)
    · -- a point: the capsule is `{c}`
      ext x
      rw [HPolytope.mem_ofPoint_iff, aux_mem_of_r_eq_zero hpt.2, hpt.1]
      simp only [smul_zero, sub_eq_zero]
      exact ⟨fun hx => ⟨0, ⟨by norm_num, by norm_num⟩, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
    · exact aux_hPolytope_line C hline fun hg => hpt ⟨hg, hline⟩
    · exfalso
      rcases h with h | h
      · exact hm (by omega)
      · exact hline (le_antisymm h (not_lt.mp hr))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
