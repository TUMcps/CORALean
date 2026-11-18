module

public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifyZonoInvariant
public import CORALean.ContDynamics.LinearSys.Definitions.Basic
public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopePassFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionInputFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsEqTaylorAddOfMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyGirardReduceFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonoGenSetAppend
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# One step of `LinearSys.verifyZonotopePassFloat` keeps the enclosure

From a state enclosing the system at `t` (`LinearSys.IsVerifyZonoInvariant`), a step gives one at
`t + Δt`, and a full step an output set holding `C x(t + τ)`, `τ ∈ [0, Δt]`. The carried error is
`(e^{AΔt} − D) z + e^{AΔt} ε` and the widths; `P^V(t + Δt) = e^{tA} P^V(Δt) + P^V(t)`
(`inputReach_separation_eq`), carried by `Φ` within `φ βU`. With `λ = τ/Δt`, `x(t + τ) =
(1 − λ) z + λ (z' + R) + F_τ z + G_τ u₀ + ((1 − λ) I + F_τ) ε`, `F_τ ∈ F` and `R` the carried
residual: CORA's `linComb` plus boxes; the input at `t + τ` lies in its set at `t + Δt`.

## Inputs
* `sys` – linear system
* `s` – positive float scales
* `u₀` – float box of the constant input
* `MU` – float box of the generators of the input
* `C` – float output matrix
* `specs` – float specifications
* `st` – float state at `t`
* `g` – step of the grid

## Hypotheses
* `hs` – the scales are positive
* `hu` – the constant input lies in its box
* `hM` – the input's generators lie in their box
* `hinv` – the state encloses the system at `t`

## Conclusion
* for a returned step, `Δt > 0`, its state encloses the system at `t + Δt`, and its output set
  holds every output over the step
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- A left fold of upward additions is at least its seed plus the sum of the terms. -/
private theorem LinearSys.aux_le_foldl {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun x => toReal (f x)).sum
        ≤ toReal (L.foldl (fun acc x => addUp acc (f x)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (addUp a (f x))
    linarith [add_le_addUp a (f x)]

omit [ToRat 𝕋] in
/-- A point of a box is within the half-width of its midpoint. -/
private theorem LinearSys.aux_mid {I : Interval (Vec 𝕋 n)} {x : Vec ℝ n} (hx : x ∈ I.toSet)
    (i : Fin n) : -- --- CONCL ---
    |x i - toReal ((LinearSys.step_verifyMidFloat I).1 i)|
      ≤ toReal ((LinearSys.step_verifyMidFloat I).2 i) := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (Interval.mem_vec_iff.mp hx) i
  simp only [LinearSys.step_verifyMidFloat, Interval.materialise_eq, Interval.point]
  set mid := addUp (I.inf i) (half (subUp (I.sup i) (I.inf i)))
  rw [toReal_maximum, abs_le]
  have a := sub_le_subUp (I.sup i) mid
  have b := sub_le_subUp mid (I.inf i)
  constructor
  · linarith [le_max_right (toReal (subUp (I.sup i) mid)) (toReal (subUp mid (I.inf i)))]
  · linarith [le_max_left (toReal (subUp (I.sup i) mid)) (toReal (subUp mid (I.inf i)))]

omit [ToRat 𝕋] in
/-- The real product `M x` is within the half-width of the midpoint of its box. -/
private theorem LinearSys.aux_mulVec (M : Mat 𝕋 q n) (x : Vec 𝕋 n)
    (i : Fin q) : -- --- CONCL ---
    |(toRealMat M *ᵥ toRealVec x) i - toReal ((LinearSys.step_verifyMulVecFloat M x).1 i)|
      ≤ toReal ((LinearSys.step_verifyMulVecFloat M x).2 i) := by -- --- PROOF ---
  set X : Mat 𝕋 n 1 := fun l _ => x l with hX
  have hmem := Interval.matMul_outer (Interval.point M) (Interval.point X)
    (Interval.mem_point M) (Interval.mem_point X)
  refine LinearSys.aux_mid (I := ⟨fun l => (Interval.matMul (Interval.point M)
    (Interval.point X)).inf l 0, fun l => (Interval.matMul
    (Interval.point M) (Interval.point X)).sup l 0⟩) (fun l => ?_) i
  have h := (Interval.mem_mat_iff.mp hmem) l 0
  simp only [realImage_mat] at h
  have he : (toRealMat M * toRealMat X) l 0 = (toRealMat M *ᵥ toRealVec x) l := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, toRealMat, toRealVec, hX]
  rw [he] at h
  exact h

omit [ToRat 𝕋] in
/-- Generators each within a half-width of a float one span points within the sum of the
half-widths of points the float ones span. -/
private theorem LinearSys.aux_approx {L : List (Vec ℝ n)} {M : List (Vec 𝕋 n × Vec 𝕋 n)}
    (hLM : List.Forall₂ (fun g p => ∀ i, |g i - toReal (p.1 i)| ≤ toReal (p.2 i))
      L M) : -- --- CONCL ---
    ∀ {y : Vec ℝ n}, y ∈ LinearSys.verifyZonoGenSet L →
      ∃ y' ∈ LinearSys.verifyZonoGenSet ((M.map Prod.fst).map toRealVec),
        ∀ i, |y i - y' i| ≤ (M.map fun p => toReal (p.2 i)).sum := by -- --- PROOF ---
  induction hLM with
  | nil =>
    intro y hy
    exact ⟨0, rfl, fun i => by have : y = 0 := hy; simp [this]⟩
  | @cons g pr L' M' hgp _ ih =>
    intro y hy
    obtain ⟨β, hβ, z, hz, rfl⟩ := hy
    obtain ⟨z', hz', hzz⟩ := ih hz
    refine ⟨β • toRealVec pr.1 + z', ⟨β, hβ, z', hz', rfl⟩, fun i => ?_⟩
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |β * g i - β * toRealVec pr.1 i| ≤ toReal (pr.2 i) := by
      rw [← mul_sub, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)) (by rw [one_mul]; exact hgp i)
    have := abs_add_le (β * g i - β * toRealVec pr.1 i) (z i - z' i)
    have heq : β * g i + z i - (β * toRealVec pr.1 i + z' i)
        = (β * g i - β * toRealVec pr.1 i) + (z i - z' i) := by ring
    rw [heq]
    linarith [hzz i]

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- A linear map carries the span of generators into the span of their images. -/
private theorem LinearSys.aux_genSet_mulVec (C : Mat ℝ q n) : -- --- CONCL ---
    ∀ (L : List (Vec ℝ n)) {y : Vec ℝ n}, y ∈ LinearSys.verifyZonoGenSet L →
      C *ᵥ y ∈ LinearSys.verifyZonoGenSet (L.map (C *ᵥ ·)) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro y hy; have : y = 0 := hy; simp [this, LinearSys.verifyZonoGenSet]
  | cons g L ih =>
    intro y hy
    obtain ⟨β, hβ, z, hz, rfl⟩ := hy
    exact ⟨β, hβ, C *ᵥ z, ih hz, by rw [Matrix.mulVec_add, Matrix.mulVec_smul]⟩

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- A combination of generators with coefficients in `[-1, 1]` lies in their span. -/
private theorem LinearSys.aux_sum_smul_mem_genSet {k : ℕ} (f : Fin k → Vec ℝ n)
    {α : Fin k → ℝ} (hα : ∀ j, |α j| ≤ 1) : -- --- CONCL ---
    ∑ j, α j • f j ∈ LinearSys.verifyZonoGenSet (List.ofFn f) := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSys.verifyZonoGenSet]
  | succ k ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    exact ⟨α 0, hα 0, _, ih (fun j => f j.succ) (fun j => hα j.succ), rfl⟩

omit [ToRat 𝕋] in
/-- A zonotope from boxes holds the center, the spans and the box it is given. -/
private theorem LinearSys.aux_ofBoxes {cen : Interval (Vec 𝕋 n)}
    {cols : List (Interval (Vec 𝕋 n))} {P : List (Vec 𝕋 n)} {rad : Vec 𝕋 n} {c : Vec ℝ n}
    (hc : c ∈ cen.toSet) {L : List (Vec ℝ n)} (hL : List.Forall₂ (fun g I => g ∈ I.toSet) L cols)
    {y₁ y₂ e : Vec ℝ n} (hy₁ : y₁ ∈ LinearSys.verifyZonoGenSet L)
    (hy₂ : y₂ ∈ LinearSys.verifyZonoGenSet (P.map toRealVec))
    (he : ∀ i, |e i| ≤ toReal (rad i)) : -- --- CONCL ---
    c + y₁ + y₂ + e
      ∈ (LinearSys.step_verifyZonoOfBoxesFloat cen cols P rad).toSet := by -- --- PROOF ---
  have hLM : List.Forall₂ (fun g p => ∀ i, |g i - toReal (p.1 i)| ≤ toReal (p.2 i)) L
      (cols.map LinearSys.step_verifyMidFloat) := by
    rw [List.forall₂_map_right_iff]
    exact hL.imp fun g I hg i => LinearSys.aux_mid hg i
  obtain ⟨y', hy', hyy⟩ := LinearSys.aux_approx hLM hy₁
  refine ⟨y' + y₂, ?_, (c - toRealVec (LinearSys.step_verifyMidFloat cen).1) + (y₁ - y') + e,
    fun i => ?_, by unfold LinearSys.step_verifyZonoOfBoxesFloat; dsimp only; abel⟩
  · unfold LinearSys.step_verifyZonoOfBoxesFloat
    dsimp only
    rw [List.map_append]
    exact LinearSys.add_mem_verifyZonoGenSet_append hy' hy₂
    -- the center, the spans' half-widths and the box, rounded up
  · unfold LinearSys.step_verifyZonoOfBoxesFloat
    dsimp only
    simp only [Interval.materialise_eq, Interval.point, Pi.add_apply, Pi.sub_apply]
    have h0 := LinearSys.aux_mid hc i
    have hf := LinearSys.aux_le_foldl (fun x : Vec 𝕋 n × Vec 𝕋 n => x.2 i)
      (cols.map LinearSys.step_verifyMidFloat) zero
    rw [toReal_zero, zero_add] at hf
    have ha := add_le_addUp (rad i) ((LinearSys.step_verifyMidFloat cen).2 i)
    have hb := add_le_addUp (addUp (rad i) ((LinearSys.step_verifyMidFloat cen).2 i))
      ((cols.map LinearSys.step_verifyMidFloat).foldl (fun acc x => addUp acc (x.2 i)) zero)
    have := abs_add_le (c i - toRealVec (LinearSys.step_verifyMidFloat cen).1 i + (y₁ i - y' i))
      (e i)
    have := abs_add_le (c i - toRealVec (LinearSys.step_verifyMidFloat cen).1 i) (y₁ i - y' i)
    simp only [toRealVec] at *
    linarith [hyy i, he i]

omit [ToRat 𝕋] in
/-- The image `C T` holds `C x` for every point `x` of `T`. -/
private theorem LinearSys.aux_map (C : Mat 𝕋 q n) {T : LinearSys.VerifyZono 𝕋 n} {x : Vec ℝ n}
    (hx : x ∈ T.toSet) : -- --- CONCL ---
    toRealMat C *ᵥ x ∈ (LinearSys.step_verifyZonoMapFloat C T).toSet := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  set cm := LinearSys.step_verifyMulVecFloat C T.c
  set gm := T.G.map (LinearSys.step_verifyMulVecFloat C)
  set bm := (List.finRange n).map fun i =>
    LinearSys.step_verifyMulVecFloat C fun l => if l = i then T.r i else zero
  -- the generators' images, then the box as the generators `C eᵢ rᵢ`
  have hG : List.Forall₂ (fun g p => ∀ i, |g i - toReal (p.1 i)| ≤ toReal (p.2 i))
      ((T.G.map toRealVec).map (toRealMat C *ᵥ ·)) gm := by
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun g _ i => LinearSys.aux_mulVec C g i
  set ub : Fin n → Vec ℝ n := fun i l => if l = i then toReal (T.r i) else 0
  have hB : List.Forall₂ (fun g p => ∀ i, |g i - toReal (p.1 i)| ≤ toReal (p.2 i))
      ((List.finRange n).map fun i => toRealMat C *ᵥ ub i) bm := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun i _ l => ?_
    have h := LinearSys.aux_mulVec C (fun l => if l = i then T.r i else zero) l
    have hu : toRealVec (fun l => if l = i then T.r i else (zero : 𝕋)) = ub i := by
      funext l; simp only [toRealVec, ub]; split_ifs <;> simp [toReal_zero]
    rwa [hu] at h
  obtain ⟨y', hy', hyy⟩ := LinearSys.aux_approx hG (LinearSys.aux_genSet_mulVec _ _ hy)
  -- `C e = Σᵢ βᵢ C eᵢ rᵢ`
  have hbe : toRealMat C *ᵥ e ∈ LinearSys.verifyZonoGenSet
      ((List.finRange n).map fun i => toRealMat C *ᵥ ub i) := by
    set β : Fin n → ℝ := fun i => if toReal (T.r i) = 0 then 0 else e i / toReal (T.r i)
    have hβ : ∀ i, |β i| ≤ 1 := by
      intro i
      simp only [β]
      split_ifs with h0
      · simp
      · have hr : 0 < toReal (T.r i) := lt_of_le_of_ne (le_trans (abs_nonneg _) (he i))
          (Ne.symm h0)
        rw [abs_div, abs_of_pos hr, div_le_one hr]
        exact he i
    -- the box as the combination of its columns `C eᵢ rᵢ`
    have hsum : toRealMat C *ᵥ e = ∑ i, β i • (toRealMat C *ᵥ ub i) := by
      have he' : e = ∑ i, β i • ub i := by
        funext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ub]
        rw [Finset.sum_eq_single l (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero])
          (by simp), if_pos rfl]
        simp only [β]
        split_ifs with h0
        · have := he l; rw [h0] at this; simp only [zero_mul]
          exact abs_nonpos_iff.mp this
        · field_simp
      rw [he', Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    rw [hsum, ← List.ofFn_eq_map]
    exact LinearSys.aux_sum_smul_mem_genSet _ hβ
  -- the image's spans, then the center and the box
  obtain ⟨b', hb', hbb⟩ := LinearSys.aux_approx hB hbe
  refine ⟨y' + b', ?_, (toRealMat C *ᵥ toRealVec T.c - toRealVec cm.1)
      + (toRealMat C *ᵥ y - y') + (toRealMat C *ᵥ e - b'), fun i => ?_, ?_⟩
  · unfold LinearSys.step_verifyZonoMapFloat
    dsimp only
    rw [List.map_append, List.map_append]
    exact LinearSys.add_mem_verifyZonoGenSet_append hy' hb'
    -- within the summed half-widths
  · unfold LinearSys.step_verifyZonoMapFloat
    dsimp only
    simp only [Interval.materialise_eq, Interval.point, Pi.add_apply, Pi.sub_apply]
    have h0 := LinearSys.aux_mulVec C T.c i
    have hf := LinearSys.aux_le_foldl (fun x : Vec 𝕋 q × Vec 𝕋 q => x.2 i) (gm ++ bm) zero
    rw [toReal_zero, zero_add, List.map_append, List.sum_append] at hf
    have ha := add_le_addUp (cm.2 i) ((gm ++ bm).foldl (fun acc x => addUp acc (x.2 i)) zero)
    have := abs_add_le ((toRealMat C *ᵥ toRealVec T.c) i - toRealVec cm.1 i
      + ((toRealMat C *ᵥ y) i - y' i)) ((toRealMat C *ᵥ e) i - b' i)
    have := abs_add_le ((toRealMat C *ᵥ toRealVec T.c) i - toRealVec cm.1 i)
      ((toRealMat C *ᵥ y) i - y' i)
    simp only [toRealVec] at *
    linarith [hyy i, hbb i]
  · unfold LinearSys.step_verifyZonoMapFloat
    dsimp only
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
    abel

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- A row sum of a matrix is at most its norm. -/
private theorem LinearSys.aux_rowSum_le_norm (N : Mat ℝ n n) (i : Fin n) : -- --- CONCL ---
    ∑ k, |N i k| ≤ ‖N‖ := by -- --- PROOF ---
  rw [Matrix.linfty_opNorm_def]
  have h : (∑ k, ‖N i k‖₊) ≤ Finset.univ.sup fun i => ∑ k, ‖N i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖N i k‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  rw [NNReal.coe_sum] at h'
  simpa [coe_nnnorm, Real.norm_eq_abs] using h'

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- `|xₖ| ≤ h sₖ` and `‖S⁻¹ M S‖ ≤ a` give `|(M x)ᵢ| ≤ a h sᵢ`. -/
private theorem LinearSys.aux_scaled {s : Vec ℝ n} (hs : ∀ i, 0 < s i) {M : Mat ℝ n n} {a h : ℝ}
    (hM : ‖Real.MatExp.scaleConj s M‖ ≤ a) (hh : 0 ≤ h) {x : Vec ℝ n}
    (hx : ∀ k, |x k| ≤ h * s k) (i : Fin n) : -- --- CONCL ---
    |(M *ᵥ x) i| ≤ a * h * s i := by -- --- PROOF ---
  have happ : ∀ k, Real.MatExp.scaleConj s M i k = M i k * s k / s i := fun k => by
    simp [Real.MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring
  have hrow := LinearSys.aux_rowSum_le_norm (Real.MatExp.scaleConj s M) i
  have hsi := hs i
  calc |(M *ᵥ x) i| = |∑ k, M i k * x k| := rfl
    _ ≤ ∑ k, |M i k| * |x k| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k, |M i k| * (h * s k) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
    _ = (∑ k, |Real.MatExp.scaleConj s M i k|) * h * s i := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [happ, abs_div, abs_mul, abs_of_pos (hs k), abs_of_pos hsi]
        field_simp
    _ ≤ a * h * s i := by
        have := le_trans hrow hM
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hh) hsi.le

omit [ToRat 𝕋] in
/-- The float scaled norm of `M` bounds the balanced norm of a matrix below `|M|`. -/
private theorem LinearSys.aux_norm {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) (M : Mat 𝕋 n n)
    {X : Mat ℝ n n} (hX : ∀ j k, |X j k| ≤ |toReal (M j k)|) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) X‖
      ≤ toReal (LinearSys.step_verifyScaledNormFloat s M) := by -- --- PROOF ---
  set f : Fin n → 𝕋 := fun j => sumUp fun k => divUp (mulUp (absolute (M j k)) (s k)) (s j)
    with hf
  have hnn : 0 ≤ toReal (LinearSys.step_verifyScaledNormFloat s M) := by
    unfold LinearSys.step_verifyScaledNormFloat; rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _
  refine Real.MatExp.norm_le_of_sum_abs_le _ hnn fun j => ?_
  -- each row sum of the balanced `X` within the float row sum
  have hrow : ∑ k, |Real.MatExp.scaleConj (toRealVec s) X j k| ≤ toReal (f j) := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_sumUp _)
    have hsj := hs j
    have hsk := hs k
    have happ : Real.MatExp.scaleConj (toRealVec s) X j k
        = X j k * toReal (s k) / toReal (s j) := by
      simp [Real.MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul, toRealVec]; ring
    rw [happ, abs_div, abs_mul, abs_of_pos hsk, abs_of_pos hsj]
    have h1 := mul_le_mulUp (absolute (M j k)) (s k)
    rw [toReal_absolute] at h1
    refine le_trans (div_le_div_of_nonneg_right ?_ hsj.le) (div_le_divUp _ _ hsj)
    exact le_trans (mul_le_mul_of_nonneg_right (hX j k) hsk.le) h1
  refine le_trans hrow (le_trans (le_maximumOver f j) ?_)
  unfold LinearSys.step_verifyScaledNormFloat; rw [toReal_maximum]; exact le_max_right _ _

omit [ToRat 𝕋] in
/-- `|xᵢ| ≤ vᵢ` gives `|xᵢ| ≤ ν sᵢ` for `ν = max(0, maxᵢ vᵢ/sᵢ)` rounded up. -/
private theorem LinearSys.aux_scaledVec {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) (v : Vec 𝕋 n)
    {x : Vec ℝ n} (hx : ∀ i, |x i| ≤ toReal (v i)) (i : Fin n) : -- --- CONCL ---
    |x i| ≤ toReal (LinearSys.step_verifyScaledVecFloat s v) * toReal (s i) := by -- --- PROOF ---
  have hsi := hs i
  have h1 : toReal (v i) / toReal (s i) ≤ toReal (LinearSys.step_verifyScaledVecFloat s v) := by
    refine le_trans (div_le_divUp _ _ hsi) (le_trans (le_maximumOver (fun i => divUp (v i) (s i))
      i) ?_)
    unfold LinearSys.step_verifyScaledVecFloat; rw [toReal_maximum]; exact le_max_right _ _
  rw [div_le_iff₀ hsi] at h1
  exact le_trans (hx i) h1

omit [ToRat 𝕋] in
/-- The float scaled vector norm is nonnegative. -/
private theorem LinearSys.aux_scaledVec_nonneg (s v : Vec 𝕋 n) :
    0 ≤ toReal (LinearSys.step_verifyScaledVecFloat s v) := by
  unfold LinearSys.step_verifyScaledVecFloat; rw [toReal_maximum, toReal_zero]
  exact le_max_left _ _

omit [ToRat 𝕋] in
/-- The float scaled norm is nonnegative. -/
private theorem LinearSys.aux_norm_nonneg (s : Vec 𝕋 n) (M : Mat 𝕋 n n) :
    0 ≤ toReal (LinearSys.step_verifyScaledNormFloat s M) := by
  unfold LinearSys.step_verifyScaledNormFloat; rw [toReal_maximum, toReal_zero]
  exact le_max_left _ _

/-- What the input's boxes enclose: `T`'s conclusion of `LinearSys.verifyInputSolutionFloat_mem`. -/
private def LinearSys.aux_inputFacts (sys : LinearSys 𝕋 n) (Δt : 𝕋)
    (I : LinearSys.VerifyInputSolution 𝕋 n p) (u0r : Mat ℝ n 1) (Mr : Mat ℝ n p) : Prop :=
  Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) * u0r ∈ I.w.toSet ∧
  ∃ X : Fin I.V.length → Mat ℝ n p, (∀ i, X i ∈ (I.V[i.1]).toSet) ∧ (∑ i, X i) ∈ I.Vs.toSet ∧
    (∀ l, ∑ c, |(Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) * Mr) l c
      - (∑ i, X i) l c| ≤ toReal (I.ρ l)) ∧
    ∀ z ∈ sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (toReal Δt),
      ∃ b : Fin I.V.length → Fin p → ℝ, (∀ i c, |b i c| ≤ 1) ∧ ∃ y : Vec ℝ n,
        (∀ l, |y l| ≤ toReal (I.ρ l)) ∧ z = (∑ i, X i *ᵥ b i) + y

omit [ToRat 𝕋] in
/-- A float that tests zero both ways reads as zero. -/
private theorem LinearSys.aux_isZero {x : 𝕋} (h : (le x FloatOps.zero && le
    FloatOps.zero x) = true) : -- --- CONCL ---
    toReal x = 0 := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ ▸ h
  have a := toReal_le_of_le h1
  have b := toReal_le_of_le h2
  rw [toReal_zero] at a b
  linarith

omit [ToRat 𝕋] in
/-- The boxes of a step enclose the input: the input solution's facts and `G u₀`. -/
private theorem LinearSys.aux_inputBoxes_mem (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 < toReal Δt) {u₀ : Interval (Mat 𝕋 n 1)}
    {MU : Interval (Mat 𝕋 n p)} {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n p}
    (hM : Mr ∈ MU.toSet) {I : LinearSys.VerifyInputSolution 𝕋 n p} {g : Interval (Mat 𝕋 n 1)}
    (hbox : LinearSys.step_verifyZonoInputFloat sys.A s Δt u₀ MU = some (I, g)) : -- --- CONCL ---
    LinearSys.aux_inputFacts sys Δt I u0r Mr ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal Δt →
      (Real.MatExp.expIntegral (toRealMat sys.A) τ
        - (τ / toReal Δt) • Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt)) * u0r
        ∈ g.toSet := by -- --- PROOF ---
  unfold LinearSys.step_verifyZonoInputFloat at hbox
  dsimp only at hbox
  split at hbox
  rotate_left
  · simp at hbox
  rename_i I' g' hI hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hbox
  obtain ⟨rfl, rfl⟩ := hbox
  -- an input whose box tests zero is zero
  have hu0 : (!(List.finRange n).all fun l => (le (u₀.inf l 0) FloatOps.zero
      && le FloatOps.zero (u₀.inf l 0)) && (le (u₀.sup l 0) FloatOps.zero
      && le FloatOps.zero (u₀.sup l 0))) = false → u0r = 0 := by
    intro h
    simp only [Bool.not_eq_false', List.all_eq_true, List.mem_finRange, forall_const,
      Bool.and_eq_true] at h
    funext l c
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hu l 0
    have a := LinearSys.aux_isZero (Bool.and_eq_true _ _ ▸ (h l).1)
    have b := LinearSys.aux_isZero (Bool.and_eq_true _ _ ▸ (h l).2)
    simp only [Matrix.zero_apply]
    linarith
  -- likewise the generators of the input
  have hM0 : (!(List.finRange n).all fun l => (List.finRange p).all fun c =>
      (le (MU.inf l c) FloatOps.zero && le FloatOps.zero (MU.inf l c))
      && (le (MU.sup l c) FloatOps.zero && le FloatOps.zero (MU.sup l c))) = false → Mr = 0 := by
    intro h
    simp only [Bool.not_eq_false', List.all_eq_true, List.mem_finRange, forall_const,
      Bool.and_eq_true] at h
    funext l c
    obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hM l c
    have a := LinearSys.aux_isZero (Bool.and_eq_true _ _ ▸ (h l c).1)
    have b := LinearSys.aux_isZero (Bool.and_eq_true _ _ ▸ (h l c).2)
    simp only [Matrix.zero_apply]
    linarith
  -- the input's facts, or the zero input's
  constructor
  · split_ifs at hI with hhas
    · exact LinearSys.verifyInputSolutionFloat_mem sys hs hΔt hu hM I' (Option.mem_def.mpr hI)
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hhas
      have hu' := hu0 hhas.1
      have hM' := hM0 hhas.2
      simp only [Option.some.injEq] at hI
      subst hI hu' hM'
      refine ⟨Interval.mem_mat_iff.mpr fun l c => ?_, fun i => i.elim0, fun i => i.elim0,
        Interval.mem_mat_iff.mpr fun l c => ?_, fun l => ?_, ?_⟩
      · simp [Interval.point, toReal_zero]
      · simp [Interval.point, toReal_zero]
      · simp [toReal_zero]
      -- the zero input contributes the remainder only
      intro z hz
      obtain ⟨b, -, y, hy, hzeq⟩ :=
        sys.exists_eq_taylor_add_of_mem_inputReach (0 : Mat ℝ n p) hΔt 0 hz
      refine ⟨fun i => i.elim0, fun i => i.elim0, y, fun l => ?_, ?_⟩
      · have h := hy l
        simp only [Matrix.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero] at h
        simp only [toReal_zero]; exact h
      · rw [hzeq]; simp
    -- `G u₀`, or nothing without a constant input
  · intro τ hτ0 hτ1
    split_ifs at hg with hhas
    · obtain ⟨⟨η, Gm⟩, hGm, rfl⟩ := Option.map_eq_some_iff.mp hg
      simp only [Interval.materialiseMat_eq]
      exact Interval.matMul_outer _ _ (MatExp.expIntegralDiff_mem_verifyCorrectionInputFloat
        sys.A hs hΔt (η, Gm) (Option.mem_def.mpr hGm) τ hτ0 hτ1) hu
    · simp only [Bool.not_eq_true] at hhas
      rw [hu0 hhas]
      simp only [Option.some.injEq] at hg
      subst hg
      exact Interval.mem_mat_iff.mpr fun l c => by simp [Interval.point, toReal_zero]

omit [ToRat 𝕋] in
/-- The real product `M x` lies in the box of the product of the points, entry by entry. -/
private theorem LinearSys.aux_mulVec_mem (M : Mat 𝕋 q n) (x : Vec 𝕋 n)
    (l : Fin q) : -- --- CONCL ---
    toReal ((Interval.matMul (Interval.point M) (Interval.point fun l (_ : Fin 1) => x l)).inf l 0)
      ≤ (toRealMat M *ᵥ toRealVec x) l ∧
    (toRealMat M *ᵥ toRealVec x) l
      ≤ toReal ((Interval.matMul (Interval.point M) (Interval.point fun l (_ : Fin 1) => x l)).sup
        l 0) := by -- --- PROOF ---
  set X : Mat 𝕋 n 1 := fun l _ => x l with hX
  have hmem := Interval.matMul_outer (Interval.point M) (Interval.point X)
    (Interval.mem_point M) (Interval.mem_point X)
  have h := (Interval.mem_mat_iff.mp hmem) l 0
  simp only [realImage_mat] at h
  have he : (toRealMat M * toRealMat X) l 0 = (toRealMat M *ᵥ toRealVec x) l := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, toRealMat, toRealVec, hX]
  rw [he] at h
  exact h

omit [ToRat 𝕋] in
/-- The magnitude of the carried zonotope bounds its points. -/
private theorem LinearSys.aux_mag (st : LinearSys.VerifyZonoState 𝕋 n m) {b : Fin m → ℝ}
    (hb : ∀ j, |b j| ≤ 1) (l : Fin n) : -- --- CONCL ---
    |(toRealVec st.c + toRealMat st.G *ᵥ b) l| ≤ toReal (LinearSys.step_verifyZonoMagFloat st l)
      := by -- --- PROOF ---
  simp only [LinearSys.step_verifyZonoMagFloat, Interval.materialise_eq, Interval.point]
  have h1 := add_le_addUp (absolute (st.c l)) (sumUp fun j => absolute (st.G l j))
  have h2 := sum_le_sumUp fun j => absolute (st.G l j)
  rw [toReal_absolute] at h1
  have h3 : |(toRealMat st.G *ᵥ b) l| ≤ ∑ j, toReal (absolute (st.G l j)) := by
    rw [show (toRealMat st.G *ᵥ b) l = ∑ j, toRealMat st.G l j * b j from rfl]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, toReal_absolute]
    exact le_trans (mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)) (by simp [toRealMat])
  have := abs_add_le (toRealVec st.c l) ((toRealMat st.G *ᵥ b) l)
  simp only [Pi.add_apply, toRealVec] at *
  linarith

omit [ToRat 𝕋] in
/-- `‖S⁻¹ e^{AΔt} S‖ ≤ ‖S⁻¹ D S‖ + r` rounded up. -/
private theorem LinearSys.aux_nE {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) {E : Mat ℝ n n}
    {D : Mat 𝕋 n n} {r : 𝕋}
    (hD : ‖Real.MatExp.scaleConj (toRealVec s) (E - toRealMat D)‖ ≤ toReal r) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) E‖
      ≤ toReal (addUp (LinearSys.step_verifyScaledNormFloat s D) r) := by -- --- PROOF ---
  have hsplit : Real.MatExp.scaleConj (toRealVec s) E = Real.MatExp.scaleConj (toRealVec s)
      (toRealMat D) + Real.MatExp.scaleConj (toRealVec s) (E - toRealMat D) := by
    simp only [Real.MatExp.scaleConj, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add (LinearSys.aux_norm hs D
    fun j k => le_rfl) hD) (add_le_addUp _ _))

omit [ToRat 𝕋] in
set_option maxHeartbeats 1000000 in -- the carry is unfolded with its `let`s
/-- The carried zonotope: its residual against `e^{AΔt} z + w` and the invariant's first two parts
at `t + Δt`. -/
private theorem LinearSys.aux_carry {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) {E : Mat ℝ n n}
    {D : Mat 𝕋 n n} {r : 𝕋}
    (hD : ‖Real.MatExp.scaleConj (toRealVec s) (E - toRealMat D)‖ ≤ toReal r)
    {w : Interval (Mat 𝕋 n 1)} {wr : Vec ℝ n}
    (hw : ∀ l, toReal (w.inf l 0) ≤ wr l ∧ wr l ≤ toReal (w.sup l 0))
    (st : LinearSys.VerifyZonoState 𝕋 n m) (hh : 0 ≤ toReal st.h)
    (hφ : 0 ≤ toReal st.φ) : -- --- CONCL ---
    let st' := LinearSys.step_verifyZonoCarryFloat s D r w st
    0 ≤ toReal st'.h ∧ 0 ≤ toReal st'.φ ∧ st'.P = st.P ∧ st'.b = st.b ∧ st'.ρ = st.ρ ∧
    (∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ ε : Vec ℝ n, (∀ k, |ε k| ≤ toReal st.h * toReal (s k)) →
      ∀ i, |(E *ᵥ (toRealVec st.c + toRealMat st.G *ᵥ b + ε) + wr
        - (toRealVec st'.c + toRealMat st'.G *ᵥ b)) i| ≤ toReal st'.h * toReal (s i)) ∧
    (∀ X : Mat ℝ n n, (∀ a : ℝ, 0 ≤ a → ∀ x : Vec ℝ n, (∀ k, |x k| ≤ a * toReal (s k)) → ∀ i,
      |((X - toRealMat st.Φ) *ᵥ x) i| ≤ toReal st.φ * a * toReal (s i)) →
      ∀ a : ℝ, 0 ≤ a → ∀ x : Vec ℝ n, (∀ k, |x k| ≤ a * toReal (s k)) → ∀ i,
      |((E * X - toRealMat st'.Φ) *ᵥ x) i| ≤ toReal st'.φ * a * toReal (s i)) := by -- --- PROOF ---
  intro st'
  have hsr : ∀ i, 0 < toRealVec s i := hs
  have hr0 : 0 ≤ toReal r := le_trans (norm_nonneg _) hD
  have hnE := LinearSys.aux_nE hs hD
  set nE := addUp (LinearSys.step_verifyScaledNormFloat s D) r with hnEdef
  have hnE0 : 0 ≤ toReal nE := le_trans (norm_nonneg _) hnE
  set v := LinearSys.step_verifyZonoMagFloat st with hv
  set wm := LinearSys.step_verifyMidFloat
    (⟨fun l => w.inf l 0, fun l => w.sup l 0⟩ : Interval (Vec 𝕋 n)) with hwm
  set Dc := Interval.matMul (Interval.point D) (Interval.point fun l (_ : Fin 1) => st.c l)
  set c' : Interval (Vec 𝕋 n) := (⟨fun l => addDown (Dc.inf l 0) (wm.1 l),
    fun l => addUp (Dc.sup l 0) (wm.1 l)⟩ : Interval (Vec 𝕋 n)).materialise with hc'
  set G' := (Interval.matMul (Interval.point D) (Interval.point st.G)).materialiseMat with hG'
  set gapv : Vec 𝕋 n := fun l => addUp (addUp (subUp (c'.sup l) (c'.inf l))
    (sumUp fun j => subUp (G'.sup l j) (G'.inf l j))) (wm.2 l) with hgapv
  set gap := LinearSys.step_verifyScaledVecFloat s gapv with hgap
  set Φ' := (Interval.matMul (Interval.point D) (Interval.point st.Φ)).materialiseMat with hΦ'
  set sv := LinearSys.step_verifyScaledVecFloat s v with hsv                -- ≥ ‖S⁻¹ |z|‖
  set nΦ := LinearSys.step_verifyScaledNormFloat s st.Φ with hnΦ
  set nW := LinearSys.step_verifyScaledNormFloat s fun j l => subUp (Φ'.sup j l) (Φ'.inf j l)
    with hnW                                                               -- ≥ the width of D Φ
  set h₁ := addUp (mulUp nE st.h) (mulUp r sv) with hh₁
  set φ₁ := addUp (mulUp nE st.φ) (mulUp r nΦ) with hφ₁
  have hst'c : st'.c = c'.sup := rfl
  have hst'G : st'.G = G'.sup := rfl
  have hst'h : st'.h = addUp h₁ gap := rfl
  have hst'Φ : st'.Φ = Φ'.sup := rfl
  have hst'φ : st'.φ = addUp φ₁ nW := rfl
  have hsv0 := LinearSys.aux_scaledVec_nonneg s v
  have hgap0 := LinearSys.aux_scaledVec_nonneg s gapv
  have hnΦ0 := LinearSys.aux_norm_nonneg s st.Φ
  have hnW0 := LinearSys.aux_norm_nonneg s fun j l => subUp (Φ'.sup j l) (Φ'.inf j l)
  -- the error bounds are nonnegative
  have hh' : 0 ≤ toReal st'.h := by
    rw [hst'h]
    have a := mul_le_mulUp nE st.h
    have b := mul_le_mulUp r sv
    have c := add_le_addUp (mulUp nE st.h) (mulUp r sv)
    have d := add_le_addUp h₁ gap
    nlinarith [mul_nonneg hnE0 hh, mul_nonneg hr0 hsv0]
  have hφ' : 0 ≤ toReal st'.φ := by
    rw [hst'φ]
    have a := mul_le_mulUp nE st.φ
    have b := mul_le_mulUp r nΦ
    have c := add_le_addUp (mulUp nE st.φ) (mulUp r nΦ)
    have d := add_le_addUp φ₁ nW
    nlinarith [mul_nonneg hnE0 hφ, mul_nonneg hr0 hnΦ0]
  refine ⟨hh', hφ', rfl, rfl, rfl, fun b hb ε hε i => ?_, fun X hX a ha x hx i => ?_⟩
  · -- `(E − D) z + E ε + (w − w̃) + (D c + w̃ − c') + (D G − G') b`
    set z := toRealVec st.c + toRealMat st.G *ᵥ b with hz
    have hzv : ∀ k, |z k| ≤ toReal sv * toReal (s k) :=
      LinearSys.aux_scaledVec hs v (LinearSys.aux_mag st hb)
    have h1 := LinearSys.aux_scaled hsr hD hsv0 hzv i
    have h2 := LinearSys.aux_scaled hsr hnE hh hε i
    -- the widths, entry by entry
    have hgw : ∀ l, |(wr - toRealVec wm.1) l + (toRealMat D *ᵥ toRealVec st.c + toRealVec wm.1
        - toRealVec c'.sup) l + ((toRealMat D * toRealMat st.G - toRealMat G'.sup) *ᵥ b) l|
        ≤ toReal (gapv l) := by
      intro l
      have hm := LinearSys.aux_mid (I := ⟨fun l => w.inf l 0, fun l => w.sup l 0⟩) (x := wr)
        (fun l => hw l) l
      obtain ⟨hdc1, hdc2⟩ := LinearSys.aux_mulVec_mem D st.c l
      have hcl : toReal (c'.inf l) = toReal (addDown (Dc.inf l 0) (wm.1 l)) := by
        rw [hc', Interval.materialise_eq]
      have hcu : toReal (c'.sup l) = toReal (addUp (Dc.sup l 0) (wm.1 l)) := by
        rw [hc', Interval.materialise_eq]
      have ad := addDown_le_add (Dc.inf l 0) (wm.1 l)
      have au := add_le_addUp (Dc.sup l 0) (wm.1 l)
      have hsc := sub_le_subUp (c'.sup l) (c'.inf l)
      -- `D G` in its box, then its residual along `b`
      have hGm : toRealMat D * toRealMat st.G ∈ G'.toSet := by
        rw [hG', Interval.materialiseMat_eq]
        exact Interval.matMul_outer _ _ (Interval.mem_point D) (Interval.mem_point st.G)
      have hGb : |((toRealMat D * toRealMat st.G - toRealMat G'.sup) *ᵥ b) l|
          ≤ toReal (sumUp fun j => subUp (G'.sup l j) (G'.inf l j)) := by
        rw [show ((toRealMat D * toRealMat st.G - toRealMat G'.sup) *ᵥ b) l = ∑ j,
          (toRealMat D * toRealMat st.G - toRealMat G'.sup) l j * b j from rfl]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
          (sum_le_sumUp _))
        obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp hGm) l j
        have := sub_le_subUp (G'.sup l j) (G'.inf l j)
        rw [abs_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)) ?_
        rw [mul_one, Matrix.sub_apply, abs_le]
        simp only [toRealMat]
        constructor <;> linarith
      -- the center's residual within the widths of `c'`
      have e1 := add_le_addUp (addUp (subUp (c'.sup l) (c'.inf l))
        (sumUp fun j => subUp (G'.sup l j) (G'.inf l j))) (wm.2 l)
      have e2 := add_le_addUp (subUp (c'.sup l) (c'.inf l))
        (sumUp fun j => subUp (G'.sup l j) (G'.inf l j))
      have hdc : |(toRealMat D *ᵥ toRealVec st.c + toRealVec wm.1 - toRealVec c'.sup) l|
          ≤ toReal (subUp (c'.sup l) (c'.inf l)) := by
        simp only [Pi.add_apply, Pi.sub_apply, toRealVec]
        rw [abs_le]; constructor <;> linarith
      simp only [hgapv]
      have := abs_add_le ((wr - toRealVec wm.1) l + (toRealMat D *ᵥ toRealVec st.c
        + toRealVec wm.1 - toRealVec c'.sup) l)
        (((toRealMat D * toRealMat st.G - toRealMat G'.sup) *ᵥ b) l)
      have := abs_add_le ((wr - toRealVec wm.1) l) ((toRealMat D *ᵥ toRealVec st.c
        + toRealVec wm.1 - toRealVec c'.sup) l)
      have hm' : |(wr - toRealVec wm.1) l| ≤ toReal (wm.2 l) := hm
      linarith
    -- the three parts of the residual
    have h3 := LinearSys.aux_scaledVec hs gapv hgw i
    have hsplit : E *ᵥ (z + ε) + wr - (toRealVec st'.c + toRealMat st'.G *ᵥ b)
        = (E - toRealMat D) *ᵥ z + E *ᵥ ε + ((wr - toRealVec wm.1) + (toRealMat D *ᵥ toRealVec st.c
          + toRealVec wm.1 - toRealVec c'.sup) + (toRealMat D * toRealMat st.G
          - toRealMat G'.sup) *ᵥ b) := by
      rw [hst'c, hst'G, hz, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add]
      abel
    rw [hsplit]
    have := abs_add_le (((E - toRealMat D) *ᵥ z + E *ᵥ ε) i) (((wr - toRealVec wm.1)
      + (toRealMat D *ᵥ toRealVec st.c + toRealVec wm.1 - toRealVec c'.sup)
      + (toRealMat D * toRealMat st.G - toRealMat G'.sup) *ᵥ b) i)
    have := abs_add_le (((E - toRealMat D) *ᵥ z) i) ((E *ᵥ ε) i)
    simp only [Pi.add_apply] at *
    -- the scaled bound against `h'` rounded up
    rw [hst'h]
    have a := mul_le_mulUp nE st.h
    have b' := mul_le_mulUp r sv
    have c := add_le_addUp (mulUp nE st.h) (mulUp r sv)
    have d := add_le_addUp h₁ gap
    have hsi := hs i
    have hsum : toReal nE * toReal st.h + toReal r * toReal sv
        + toReal gap ≤ toReal (addUp h₁ gap) := by linarith
    have key := mul_le_mul_of_nonneg_right hsum hsi.le
    rw [add_mul, add_mul] at key
    have e1 : toRealVec s i = toReal (s i) := rfl
    rw [e1] at h1 h2
    linarith
  · -- `E (X − Φ) + (E − D) Φ + (D Φ − Φ')`
    have hsplit : (E * X - toRealMat st'.Φ) *ᵥ x = E *ᵥ ((X - toRealMat st.Φ) *ᵥ x)
        + (E - toRealMat D) *ᵥ (toRealMat st.Φ *ᵥ x)
        + (toRealMat D * toRealMat st.Φ - toRealMat Φ'.sup) *ᵥ x := by
      have hm : E * X - toRealMat Φ'.sup = E * (X - toRealMat st.Φ)
          + (E - toRealMat D) * toRealMat st.Φ + (toRealMat D * toRealMat st.Φ - toRealMat Φ'.sup)
          := by noncomm_ring
      rw [hst'Φ, hm, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
    -- the three parts, each in the scales
    have hXx := hX a ha x hx
    have hφa : 0 ≤ toReal st.φ * a := mul_nonneg hφ ha
    have h1 := LinearSys.aux_scaled hsr hnE hφa (fun k => hXx k) i
    have hΦx := LinearSys.aux_scaled hsr (LinearSys.aux_norm hs st.Φ (X := toRealMat st.Φ)
      fun j k => le_rfl) ha hx
    have hna := mul_nonneg hnΦ0 ha
    have h2 := LinearSys.aux_scaled hsr hD hna (fun k => hΦx k) i
    have hPm : toRealMat D * toRealMat st.Φ ∈ Φ'.toSet := by
      rw [hΦ', Interval.materialiseMat_eq]
      exact Interval.matMul_outer _ _ (Interval.mem_point D) (Interval.mem_point st.Φ)
    have h3 := LinearSys.aux_scaled hsr (LinearSys.aux_norm hs (fun j l => subUp (Φ'.sup j l)
      (Φ'.inf j l)) (X := toRealMat D * toRealMat st.Φ - toRealMat Φ'.sup) fun j k => by
        obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp hPm) j k
        have := sub_le_subUp (Φ'.sup j k) (Φ'.inf j k)
        rw [Matrix.sub_apply]
        refine le_trans ?_ (le_abs_self _)
        simp only [toRealMat] at g1 g2 ⊢
        rw [abs_le]; constructor <;> linarith) ha hx i
    -- summed, against `φ'` rounded up
    rw [hsplit]
    have := abs_add_le ((E *ᵥ ((X - toRealMat st.Φ) *ᵥ x) + (E - toRealMat D) *ᵥ
      (toRealMat st.Φ *ᵥ x)) i) (((toRealMat D * toRealMat st.Φ - toRealMat Φ'.sup) *ᵥ x) i)
    have := abs_add_le ((E *ᵥ ((X - toRealMat st.Φ) *ᵥ x)) i)
      (((E - toRealMat D) *ᵥ (toRealMat st.Φ *ᵥ x)) i)
    simp only [Pi.add_apply] at *
    rw [hst'φ]
    have a1 := mul_le_mulUp nE st.φ
    have b1 := mul_le_mulUp r nΦ
    have c1 := add_le_addUp (mulUp nE st.φ) (mulUp r nΦ)
    have d1 := add_le_addUp φ₁ nW
    have hsi := (hs i).le
    have hai := mul_nonneg ha hsi
    have hsum : toReal nE * toReal st.φ + toReal r * toReal nΦ + toReal nW
        ≤ toReal (addUp φ₁ nW) := by linarith
    have key := mul_le_mul_of_nonneg_right hsum hai
    rw [add_mul, add_mul] at key
    have e1 : toRealVec s i = toReal (s i) := rfl
    rw [e1] at h1 h2 h3
    -- regrouped as `(·) a sᵢ`
    have k1 : toReal nE * (toReal st.φ * a) * toReal (s i)
        = toReal nE * toReal st.φ * (a * toReal (s i)) := by ring
    have k2 : toReal r * (toReal nΦ * a) * toReal (s i)
        = toReal r * toReal nΦ * (a * toReal (s i)) := by
      ring
    have k3 : toReal nW * a * toReal (s i) = toReal nW * (a * toReal (s i)) := by ring
    have k4 : toReal (addUp φ₁ nW) * a * toReal (s i)
        = toReal (addUp φ₁ nW) * (a * toReal (s i)) := by ring
    rw [k1] at h1
    rw [k2] at h2
    rw [k3] at h3
    rw [k4]
    linarith

omit [ToRat 𝕋] in
/-- The orders carried by `Φ`: the first order's columns span the generators, within the first
order's widths and the magnitudes of the later orders. -/
private theorem LinearSys.aux_orders (Φ : Mat 𝕋 n n) : -- --- CONCL ---
    ∀ (L : List (Interval (Mat 𝕋 n p))) (X : Fin L.length → Mat ℝ n p),
      (∀ i, X i ∈ (L[i.1]).toSet) → ∀ bb : Fin L.length → Fin p → ℝ, (∀ i c, |bb i c| ≤ 1) →
      let ord := LinearSys.step_verifyZonoOrdersFloat Φ L
      ∃ y ∈ LinearSys.verifyZonoGenSet (ord.1.map toRealVec),
        ∀ l, |((toRealMat Φ *ᵥ ∑ i, X i *ᵥ bb i) - y) l| ≤ toReal (ord.2 l) := by -- --- PROOF ---
  intro L
  cases L with
  | nil =>
    intro X _ bb _
    refine ⟨0, rfl, fun l => ?_⟩
    simp [LinearSys.step_verifyZonoOrdersFloat, toReal_zero]
  | cons X0 L' =>
    intro X hX bb hbb
    dsimp only
    simp only [LinearSys.step_verifyZonoOrdersFloat, List.map_cons]
    set P0 := (Interval.matMul (Interval.point Φ) X0).materialiseMat with hP0
    have hP0m : toRealMat Φ * X 0 ∈ P0.toSet := by
      rw [hP0, Interval.materialiseMat_eq]
      exact Interval.matMul_outer _ _ (Interval.mem_point Φ) (hX 0)
    -- the first order: Σ_c b_c (Φ X₀)_c, against the stored columns
    set col : Fin p → Vec ℝ n := fun j l => toReal (P0.sup l j) with hcol
    refine ⟨∑ j, bb 0 j • col j, ?_, fun l => ?_⟩
    · rw [List.map_ofFn]
      have := LinearSys.aux_sum_smul_mem_genSet col (fun j => hbb 0 j)
      convert this using 2
      congr 1
      funext j
      funext l
      simp [col, toRealVec, Interval.materialise_eq, Interval.point]
    · rw [show (∑ i, X i *ᵥ bb i) = X 0 *ᵥ bb 0 + ∑ i : Fin L'.length, X i.succ *ᵥ bb i.succ
        from Fin.sum_univ_succ (n := L'.length) (fun i => X i *ᵥ bb i), Matrix.mulVec_add]
      have hpt : ∀ f : Vec 𝕋 n, (Interval.point f).sup l = f l := fun _ => rfl
      rw [Interval.materialise_eq, hpt]
      -- the first order's widths
      have h0 : |(toRealMat Φ *ᵥ (X 0 *ᵥ bb 0) - ∑ j, bb 0 j • col j) l|
          ≤ toReal (sumUp fun j => subUp (P0.sup l j) (P0.inf l j)) := by
        have he : (toRealMat Φ *ᵥ (X 0 *ᵥ bb 0) - ∑ j, bb 0 j • col j) l
            = ∑ j, ((toRealMat Φ * X 0) l j - toReal (P0.sup l j)) * bb 0 j := by
          rw [Matrix.mulVec_mulVec]
          simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col,
            Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [he]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
          (sum_le_sumUp _))
        obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp hP0m) l j
        have := sub_le_subUp (P0.sup l j) (P0.inf l j)
        rw [abs_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (hbb 0 j) (abs_nonneg _)) ?_
        rw [mul_one, abs_le]
        constructor <;> linarith
      -- the later orders: their magnitudes
      have h1 : ∀ i : Fin L'.length, |(toRealMat Φ *ᵥ (X i.succ *ᵥ bb i.succ)) l|
          ≤ toReal (sumUp fun j => ((Interval.matMul (Interval.point Φ) (L'[i.1])).materialiseMat
            ).magnitudeMat l j) := by
        intro i
        have hm : toRealMat Φ * X i.succ ∈ ((Interval.matMul (Interval.point Φ)
            (L'[i.1])).materialiseMat).toSet := by
          rw [Interval.materialiseMat_eq]
          exact Interval.matMul_outer _ _ (Interval.mem_point Φ) (hX i.succ)
        rw [Matrix.mulVec_mulVec, show ((toRealMat Φ * X i.succ) *ᵥ bb i.succ) l
          = ∑ j, (toRealMat Φ * X i.succ) l j * bb i.succ j from rfl]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
          (sum_le_sumUp _))
        obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp hm) l j
        rw [abs_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (hbb i.succ j) (abs_nonneg _)) ?_
        rw [mul_one, Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
        exact abs_le_max_abs_abs g1 g2
      -- summed over the later orders
      have hf := LinearSys.aux_le_foldl (fun X : Interval (Mat 𝕋 n p) =>
        sumUp fun j => X.magnitudeMat l j)
        (L'.map fun X => (Interval.matMul (Interval.point Φ) X).materialiseMat) zero
      rw [toReal_zero, zero_add, List.map_map] at hf
      have hsum : ∑ i : Fin L'.length, |(toRealMat Φ *ᵥ (X i.succ *ᵥ bb i.succ)) l|
          ≤ (L'.map ((fun X : Interval (Mat 𝕋 n p) => toReal (sumUp fun j => X.magnitudeMat l j))
            ∘ fun X => (Interval.matMul (Interval.point Φ) X).materialiseMat)).sum := by
        rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
        exact Finset.sum_le_sum fun i _ => h1 i
      have hrest : |(toRealMat Φ *ᵥ ∑ i : Fin L'.length, X i.succ *ᵥ bb i.succ) l|
          ≤ ∑ i : Fin L'.length, |(toRealMat Φ *ᵥ (X i.succ *ᵥ bb i.succ)) l| := by
        rw [Matrix.mulVec_sum, Finset.sum_apply]
        exact Finset.abs_sum_le_sum_abs _ _
      -- the first order plus the later ones
      have hsplit : (toRealMat Φ *ᵥ (X 0 *ᵥ bb 0) + toRealMat Φ *ᵥ ∑ i : Fin L'.length,
          X i.succ *ᵥ bb i.succ - ∑ j, bb 0 j • col j) l
          = (toRealMat Φ *ᵥ (X 0 *ᵥ bb 0) - ∑ j, bb 0 j • col j) l
            + (toRealMat Φ *ᵥ ∑ i : Fin L'.length, X i.succ *ᵥ bb i.succ) l := by
        simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [hsplit]
      have := abs_add_le ((toRealMat Φ *ᵥ (X 0 *ᵥ bb 0) - ∑ j, bb 0 j • col j) l)
        ((toRealMat Φ *ᵥ ∑ i : Fin L'.length, X i.succ *ᵥ bb i.succ) l)
      have := add_le_addUp (sumUp fun j => subUp (P0.sup l j) (P0.inf l j))
        ((L'.map fun X => (Interval.matMul (Interval.point Φ) X).materialiseMat).foldl
          (fun acc (X : Interval (Mat 𝕋 n p)) => addUp acc (sumUp fun j => X.magnitudeMat l j))
          FloatOps.zero)
      linarith

omit [ToRat 𝕋] in
/-- The varying input over the step: the invariant's third part at `t + Δt`. -/
private theorem LinearSys.aux_inputStep (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    {I : LinearSys.VerifyInputSolution 𝕋 n p} {u0r : Mat ℝ n 1} {Mr : Mat ℝ n p}
    (hfacts : LinearSys.aux_inputFacts sys Δt I u0r Mr) (budget : 𝕋)
    (st : LinearSys.VerifyZonoState 𝕋 n m) {t : ℝ} (ht : 0 ≤ t) (hφ : 0 ≤ toReal st.φ)
    (hρ : 0 ≤ toReal st.ρ)
    (hΦ : ∀ a : ℝ, 0 ≤ a → ∀ x : Vec ℝ n, (∀ k, |x k| ≤ a * toReal (s k)) → ∀ i,
      |((exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ x) i| ≤ toReal st.φ * a * toReal (s i))
    (hP : ∀ y ∈ sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) t,
      ∃ y' ∈ LinearSys.verifyZonoGenSet (st.P.map toRealVec), ∃ e₁ e₂ : Vec ℝ n,
        (∀ i, |e₁ i| ≤ toReal (st.b i)) ∧ (∀ i, |e₂ i| ≤ toReal st.ρ * toReal (s i)) ∧
        y = y' + e₁ + e₂) : -- --- CONCL ---
    let inp := LinearSys.step_verifyZonoInputStepFloat s I budget st
    0 ≤ toReal inp.2.2 ∧
    ∀ y ∈ sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (t + toReal Δt),
      ∃ y' ∈ LinearSys.verifyZonoGenSet (inp.1.map toRealVec), ∃ e₁ e₂ : Vec ℝ n,
        (∀ i, |e₁ i| ≤ toReal (inp.2.1 i)) ∧ (∀ i, |e₂ i| ≤ toReal inp.2.2 * toReal (s i)) ∧
        y = y' + e₁ + e₂ := by -- --- PROOF ---
  intro inp
  set V : Set (Vec ℝ n) := (fun β => Mr *ᵥ β) '' Set.Icc (-1) 1 with hV
  set βU := LinearSys.step_verifyScaledVecFloat s fun l => addUp (I.V.foldl (fun acc X =>
    addUp acc (sumUp fun j => X.magnitudeMat l j)) zero) (I.ρ l) with hβU
  have hβU0 := LinearSys.aux_scaledVec_nonneg s (fun l => addUp (I.V.foldl (fun acc X =>
    addUp acc (sumUp fun j => X.magnitudeMat l j)) zero) (I.ρ l))
  have hinp22 : inp.2.2 = addUp st.ρ (mulUp st.φ βU) := rfl
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hinp22]
    have := add_le_addUp st.ρ (mulUp st.φ βU)
    have := mul_le_mulUp st.φ βU
    nlinarith [mul_nonneg hφ hβU0]
  -- `P^V(t + Δt) = e^{tA} P^V(Δt) + P^V(t)`
  have hbdd : Bornology.IsBounded V :=
    (isCompact_Icc.image (Matrix.mulVecLin Mr).continuous_of_finiteDimensional).isBounded
  rw [add_comm t, sys.inputReach_separation_eq hΔt.le ht hbdd] at hy
  obtain ⟨_, ⟨z, hz, rfl⟩, yo, hyo, rfl⟩ := hy
  obtain ⟨-, X, hX, -, -, hzs⟩ := hfacts
  obtain ⟨bb, hbb, yr, hyr, rfl⟩ := hzs z hz
  obtain ⟨gn, hgn, hgnb⟩ := LinearSys.aux_orders st.Φ I.V X hX bb hbb
  obtain ⟨yo', hyo', e1o, e2o, he1o, he2o, rfl⟩ := hP yo hyo
  -- the box part: the old box, the first order's widths, the later orders, `Φ y`
  set e : Vec ℝ n := e1o + (toRealMat st.Φ *ᵥ ∑ i, X i *ᵥ bb i - gn) + toRealMat st.Φ *ᵥ yr
    with he
  set ord := LinearSys.step_verifyZonoOrdersFloat st.Φ I.V
  have hebox : ∀ l, |e l| ≤ toReal ((Interval.point fun l => addUp (addUp (st.b l) (ord.2 l))
      (sumUp fun j => mulUp (absolute (st.Φ l j)) (I.ρ j))).materialise.sup l) := by
    intro l
    rw [Interval.materialise_eq]
    have hpt : ∀ f : Vec 𝕋 n, (Interval.point f).sup l = f l := fun _ => rfl
    rw [hpt]
    have h1 := hgnb l
    -- the remainder carried by `Φ`
    have h2 : |(toRealMat st.Φ *ᵥ yr) l|
        ≤ toReal (sumUp fun j => mulUp (absolute (st.Φ l j)) (I.ρ j)) := by
      rw [show (toRealMat st.Φ *ᵥ yr) l = ∑ j, toRealMat st.Φ l j * yr j from rfl]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (sum_le_sumUp _))
      have := mul_le_mulUp (absolute (st.Φ l j)) (I.ρ j)
      rw [toReal_absolute] at this
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hyr j) (abs_nonneg _)) this
    have a1 := add_le_addUp (st.b l) (ord.2 l)
    have a2 := add_le_addUp (addUp (st.b l) (ord.2 l))
      (sumUp fun j => mulUp (absolute (st.Φ l j)) (I.ρ j))
    have t1 := abs_add_le ((e1o + (toRealMat st.Φ *ᵥ ∑ i, X i *ᵥ bb i - gn)) l)
      ((toRealMat st.Φ *ᵥ yr) l)
    have t2 := abs_add_le (e1o l) ((toRealMat st.Φ *ᵥ ∑ i, X i *ᵥ bb i - gn) l)
    rw [he]
    simp only [Pi.add_apply] at t1 t2 ⊢
    linarith [he1o l]
  obtain ⟨y', hy', e', he', heq⟩ := LinearSys.mem_verifyGirardReduceFloat st.P _ _ budget hyo'
    hgn hebox
  -- the error of `Φ`: `|z| ≤ βU s`
  have hz : ∀ k, |((∑ i, X i *ᵥ bb i) + yr) k| ≤ toReal βU * toReal (s k) := by
    refine LinearSys.aux_scaledVec hs _ fun l => ?_
    have hf := LinearSys.aux_le_foldl (fun X : Interval (Mat 𝕋 n p) =>
      sumUp fun j => X.magnitudeMat l j) I.V zero
    rw [toReal_zero, zero_add] at hf
    have hsum : |(∑ i, X i *ᵥ bb i) l| ≤ (I.V.map fun X : Interval (Mat 𝕋 n p) =>
        toReal (sumUp fun j => X.magnitudeMat l j)).sum := by
      rw [← List.ofFn_getElem_eq_map, List.sum_ofFn, Finset.sum_apply]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [show (X i *ᵥ bb i) l = ∑ j, X i l j * bb i j from rfl]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (sum_le_sumUp _))
      obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp (hX i)) l j
      rw [abs_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hbb i j) (abs_nonneg _)) ?_
      rw [mul_one, Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
      exact abs_le_max_abs_abs g1 g2
    -- the orders' magnitudes plus the remainder
    have a1 := add_le_addUp (I.V.foldl (fun acc (X : Interval (Mat 𝕋 n p)) => addUp acc
      (sumUp fun j => X.magnitudeMat l j)) FloatOps.zero) (I.ρ l)
    have := abs_add_le ((∑ i, X i *ᵥ bb i) l) (yr l)
    simp only [Pi.add_apply]
    linarith [hyr l]
  have hzΦ := hΦ (toReal βU) hβU0 _ hz
  -- the reduced generators and box, the scaled error `ρ + φ βU`
  refine ⟨y', hy', e', e2o + (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ
    ((∑ i, X i *ᵥ bb i) + yr), he', fun i => ?_, ?_⟩
  · rw [hinp22]
    have a := add_le_addUp st.ρ (mulUp st.φ βU)
    have b := mul_le_mulUp st.φ βU
    have hsi := (hs i).le
    have key : (toReal st.ρ + toReal st.φ * toReal βU) * toReal (s i)
        ≤ toReal (addUp st.ρ (mulUp st.φ βU)) * toReal (s i) :=
      mul_le_mul_of_nonneg_right (by linarith) hsi
    rw [add_mul] at key
    have := abs_add_le (e2o i) (((exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ
      ((∑ i, X i *ᵥ bb i) + yr)) i)
    simp only [Pi.add_apply] at *
    linarith [he2o i, hzΦ i]
  · -- `e^{tA} z + yo = Φ z + (e^{tA} − Φ) z + yo`
    have hsplit : exp (t • toRealMat sys.A) *ᵥ ((∑ i, X i *ᵥ bb i) + yr)
        = toRealMat st.Φ *ᵥ ((∑ i, X i *ᵥ bb i) + yr)
          + (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ ((∑ i, X i *ᵥ bb i) + yr) := by
      rw [Matrix.sub_mulVec]; abel
    have heq' : yo' + gn + e = y' + e' := heq
    rw [he] at heq'
    change exp (t • toRealMat sys.A) *ᵥ ((∑ i, X i *ᵥ bb i) + yr) + (yo' + e1o + e2o) = _
    rw [hsplit, Matrix.mulVec_add]
    calc toRealMat st.Φ *ᵥ (∑ i, X i *ᵥ bb i) + toRealMat st.Φ *ᵥ yr
          + (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ ((∑ i, X i *ᵥ bb i) + yr)
          + (yo' + e1o + e2o)
        = (yo' + gn + (e1o + (toRealMat st.Φ *ᵥ ∑ i, X i *ᵥ bb i - gn)
          + toRealMat st.Φ *ᵥ yr)) + (e2o + (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ
            ((∑ i, X i *ᵥ bb i) + yr)) := by abel
      _ = y' + e' + (e2o + (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ
            ((∑ i, X i *ᵥ bb i) + yr)) := by rw [heq']

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- Two lists of functions related entry by entry. -/
private theorem LinearSys.aux_forall₂_ofFn {α β : Type} {R : α → β → Prop} : -- --- CONCL ---
    ∀ {k : ℕ} (f : Fin k → α) (g : Fin k → β), (∀ j, R (f j) (g j)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro f g _; simp
  | succ k ih =>
    intro f g h
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ fun j => h j.succ)

omit [ToRat 𝕋] in
set_option maxHeartbeats 1000000 in -- the time-interval set is unfolded with its `let`s
/-- The time-interval set holds every state over the step plus every input contribution. -/
private theorem LinearSys.aux_interval {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i))
    {F : Interval (Mat 𝕋 n n)} {gu : Interval (Mat 𝕋 n 1)}
    (st st' : LinearSys.VerifyZonoState 𝕋 n m)
    (hh : 0 ≤ toReal st.h) (hh' : 0 ≤ toReal st'.h) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {b : Fin m → ℝ} (hb : ∀ j, |b j| ≤ 1) {ε R : Vec ℝ n}
    (hε : ∀ k, |ε k| ≤ toReal st.h * toReal (s k))
    (hR : ∀ k, |R k| ≤ toReal st'.h * toReal (s k)) {Fτ : Mat ℝ n n} (hFτ : Fτ ∈ F.toSet)
    {gτ : Vec ℝ n} (hgτ : ∀ l, toReal (gu.inf l 0) ≤ gτ l ∧ gτ l ≤ toReal (gu.sup l 0))
    {y₂ e₁ e₂ : Vec ℝ n} (hy₂ : y₂ ∈ LinearSys.verifyZonoGenSet (st'.P.map toRealVec))
    (he₁ : ∀ i, |e₁ i| ≤ toReal (st'.b i))
    (he₂ : ∀ i, |e₂ i| ≤ toReal st'.ρ * toReal (s i)) : -- --- CONCL ---
    let z := toRealVec st.c + toRealMat st.G *ᵥ b
    let z' := toRealVec st'.c + toRealMat st'.G *ᵥ b
    (1 - lam) • z + lam • (z' + R) + Fτ *ᵥ z + gτ
        + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + (y₂ + e₁ + e₂)
      ∈ (LinearSys.step_verifyZonoIntervalFloat s F gu st st').toSet := by -- --- PROOF ---
  intro z z'
  have hsr : ∀ i, 0 < toRealVec s i := hs
  unfold LinearSys.step_verifyZonoIntervalFloat
  dsimp only
  set Fc := (Interval.point fun j l => addUp (F.inf j l)
    (half (subUp (F.sup j l) (F.inf j l)))).materialiseMat.sup with hFc
  set Fr := (Interval.point fun j l => maximum (subUp (F.sup j l) (Fc j l))
    (subUp (Fc j l) (F.inf j l))).materialiseMat.sup with hFr
  set wc := Interval.matMul (Interval.point Fc) (Interval.point fun l (_ : Fin 1) => st.c l)
  set WG := (Interval.matMul (Interval.point Fc) (Interval.point st.G)).materialiseMat with hWG
  set v := LinearSys.step_verifyZonoMagFloat st with hv
  set nF := LinearSys.step_verifyScaledNormFloat s fun j l => addUp (absolute (Fc j l)) (Fr j l)
  set γ := addUp FloatOps.one nF with hγ
  set e := addUp (addUp st'.h (mulUp γ st.h)) st'.ρ with he
  -- the entries of `F_τ` about `F`'s center
  have hFm := Interval.mem_mat_iff.mp hFτ
  have hFcr : ∀ j l, |Fτ j l - toReal (Fc j l)| ≤ toReal (Fr j l) := by
    intro j l
    obtain ⟨f1, f2⟩ := hFm j l
    have hFrjl : toReal (Fr j l) = max (toReal (subUp (F.sup j l) (Fc j l)))
        (toReal (subUp (Fc j l) (F.inf j l))) := by
      rw [hFr, Interval.materialiseMat_eq]; exact toReal_maximum _ _
    have a := sub_le_subUp (F.sup j l) (Fc j l)
    have b := sub_le_subUp (Fc j l) (F.inf j l)
    rw [hFrjl, abs_le]
    constructor
    · linarith [le_max_right (toReal (subUp (F.sup j l) (Fc j l)))
        (toReal (subUp (Fc j l) (F.inf j l)))]
    · linarith [le_max_left (toReal (subUp (F.sup j l) (Fc j l)))
        (toReal (subUp (Fc j l) (F.inf j l)))]
  -- `e^{τA} ε` within `γ h s`
  have hFn : ‖Real.MatExp.scaleConj (toRealVec s) Fτ‖ ≤ toReal nF := by
    refine LinearSys.aux_norm hs _ fun j k => ?_
    have := add_le_addUp (absolute (Fc j k)) (Fr j k)
    rw [toReal_absolute] at this
    have h1 := hFcr j k
    have := abs_sub_abs_le_abs_sub (Fτ j k) (toReal (Fc j k))
    exact le_trans (show |Fτ j k| ≤ toReal (addUp (absolute (Fc j k)) (Fr j k)) by linarith)
      (le_abs_self _)
  -- `((1 − λ) I + F_τ) ε` within `γ h s`
  have hεb : ∀ i, |(((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε) i|
      ≤ toReal γ * toReal st.h * toReal (s i) := by
    intro i
    have h2 := LinearSys.aux_scaled hsr hFn hh hε i
    have hsplit : (((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε) i = (1 - lam) * ε i + (Fτ *ᵥ ε) i := by
      simp [Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [hsplit]
    have hsi := hs i
    have k1 : |(1 - lam) * ε i| ≤ (1 - lam) * (toReal st.h * toReal (s i)) := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (hε i) (by linarith)
    -- `1 + ‖F_τ‖ ≤ γ`
    have hγ' : toReal FloatOps.one + toReal nF ≤ toReal γ := add_le_addUp _ _
    rw [toReal_one] at hγ'
    have hhs := mul_nonneg hh hsi.le
    have key : (1 + toReal nF) * (toReal st.h * toReal (s i))
        ≤ toReal γ * (toReal st.h * toReal (s i)) :=
      mul_le_mul_of_nonneg_right hγ' hhs
    have := abs_add_le ((1 - lam) * ε i) ((Fτ *ᵥ ε) i)
    have e1 : toRealVec s i = toReal (s i) := rfl
    rw [e1] at h2
    nlinarith
  -- the center, the generators of `linComb`, the box
  set cr := toRealVec st.c
  set cr' := toRealVec st'.c
  set Gr := toRealMat st.G
  set Gr' := toRealMat st'.G
  set Fcr := toRealMat Fc
  set ĉ : Vec ℝ n := (1 / 2 : ℝ) • (cr + cr') + Fcr *ᵥ cr + gτ with hĉ
  -- the center `(c + c')/2 + F_c c + G_τ u₀` in its box
  have hĉm : ĉ ∈ (⟨fun l => addDown (addDown (half (addDown (st.c l) (st'.c l))) (wc.inf l 0))
      (gu.inf l 0), fun l => addUp (addUp (half (addUp (st.c l) (st'.c l))) (wc.sup l 0))
      (gu.sup l 0)⟩ : Interval (Vec 𝕋 n)).toSet := by
    rw [Interval.mem_vec_iff]
    intro l
    obtain ⟨w1, w2⟩ := LinearSys.aux_mulVec_mem Fc st.c l
    obtain ⟨g1, g2⟩ := hgτ l
    have a1 := addDown_le_add (st.c l) (st'.c l)
    have a2 := add_le_addUp (st.c l) (st'.c l)
    have a3 := addDown_le_add (half (addDown (st.c l) (st'.c l))) (wc.inf l 0)
    have a4 := add_le_addUp (half (addUp (st.c l) (st'.c l))) (wc.sup l 0)
    have a5 := addDown_le_add (addDown (half (addDown (st.c l) (st'.c l))) (wc.inf l 0))
      (gu.inf l 0)
    have a6 := add_le_addUp (addUp (half (addUp (st.c l) (st'.c l))) (wc.sup l 0)) (gu.sup l 0)
    rw [toReal_half] at a3 a4
    simp only [hĉ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cr, cr', toRealVec] at w1 w2 ⊢
    simp only [Fcr] at *
    constructor <;> linarith
  -- the generators of `linComb`, each in its box
  set g₁ : Fin m → Vec ℝ n := fun j l => (Gr l j + Gr' l j) / 2 with hg₁
  set g₂ : Fin m → Vec ℝ n := fun j l => (Gr l j - Gr' l j) / 2 with hg₂
  set g₃ : Vec ℝ n := fun l => (cr l - cr' l) / 2 with hg₃
  have hL : List.Forall₂ (fun (g : Vec ℝ n) (I : Interval (Vec 𝕋 n)) => g ∈ I.toSet)
      (List.ofFn g₁ ++ List.ofFn g₂ ++ [g₃])
      ((List.ofFn fun j : Fin m => (⟨fun l => half (addDown (st.G l j) (st'.G l j)),
        fun l => half (addUp (st.G l j) (st'.G l j))⟩ : Interval (Vec 𝕋 n))) ++
      (List.ofFn fun j : Fin m => (⟨fun l => half (subDown (st.G l j) (st'.G l j)),
        fun l => half (subUp (st.G l j) (st'.G l j))⟩ : Interval (Vec 𝕋 n))) ++
      [(⟨fun l => half (subDown (st.c l) (st'.c l)), fun l => half (subUp (st.c l) (st'.c l))⟩ :
        Interval (Vec 𝕋 n))]) := by
    -- `(G + G')/2`, `(G − G')/2`, `(c − c')/2`, each between its halves rounded
    refine List.rel_append (List.rel_append (LinearSys.aux_forall₂_ofFn _ _ fun j => ?_)
      (LinearSys.aux_forall₂_ofFn _ _ fun j => ?_)) (List.Forall₂.cons ?_ List.Forall₂.nil)
    · rw [Interval.mem_vec_iff]; intro l
      have a1 := addDown_le_add (st.G l j) (st'.G l j)
      have a2 := add_le_addUp (st.G l j) (st'.G l j)
      rw [toReal_half, toReal_half]
      simp only [hg₁, Gr, Gr', toRealMat]
      constructor <;> linarith
    · rw [Interval.mem_vec_iff]; intro l
      have a1 := subDown_le_sub (st.G l j) (st'.G l j)
      have a2 := sub_le_subUp (st.G l j) (st'.G l j)
      rw [toReal_half, toReal_half]
      simp only [hg₂, Gr, Gr', toRealMat]
      constructor <;> linarith
    · rw [Interval.mem_vec_iff]; intro l
      have a1 := subDown_le_sub (st.c l) (st'.c l)
      have a2 := sub_le_subUp (st.c l) (st'.c l)
      rw [toReal_half, toReal_half]
      simp only [hg₃, cr, cr', toRealVec]
      constructor <;> linarith
  -- CORA's `linComb` as a combination, `β = 1 − 2λ`
  set β := 1 - 2 * lam with hβ
  have hβ1 : |β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  set y₁ := (∑ j, b j • g₁ j + ∑ j, (β * b j) • g₂ j) + β • g₃ with hy₁
  have hy₁m : y₁ ∈ LinearSys.verifyZonoGenSet (List.ofFn g₁ ++ List.ofFn g₂ ++ [g₃]) := by
    refine LinearSys.add_mem_verifyZonoGenSet_append (LinearSys.add_mem_verifyZonoGenSet_append
      (LinearSys.aux_sum_smul_mem_genSet _ hb)
      (LinearSys.aux_sum_smul_mem_genSet _ fun j => ?_)) ⟨β, hβ1, 0, rfl, by simp⟩
    rw [abs_mul]; exact le_trans (mul_le_mul hβ1 (hb j) (abs_nonneg _) zero_le_one) (by simp)
  -- the box: the input's, `F_c G b`, `(F_τ − F_c) z`, and the scaled errors
  set eb : Vec ℝ n := e₁ + (Fcr * Gr) *ᵥ b + (Fτ - Fcr) *ᵥ z
    + (lam • R + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + e₂) with heb
  have hzv : ∀ k, |z k| ≤ toReal (v k) := LinearSys.aux_mag st hb
  have hebm : ∀ l, |eb l| ≤ toReal (addUp (addUp (addUp (st'.b l)
      (sumUp fun j => WG.magnitudeMat l j)) ((Interval.point (mulVecUp Fr v)).materialise.sup l))
      (mulUp (s l) e)) := by
    intro l
    -- `F_c G b`
    have hWGm : Fcr * Gr ∈ WG.toSet := by
      rw [hWG, Interval.materialiseMat_eq]
      exact Interval.matMul_outer _ _ (Interval.mem_point Fc) (Interval.mem_point st.G)
    have k1 : |((Fcr * Gr) *ᵥ b) l| ≤ toReal (sumUp fun j => WG.magnitudeMat l j) := by
      rw [show ((Fcr * Gr) *ᵥ b) l = ∑ j, (Fcr * Gr) l j * b j from rfl]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (sum_le_sumUp _))
      obtain ⟨g1, g2⟩ := (Interval.mem_mat_iff.mp hWGm) l j
      rw [abs_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)) ?_
      rw [mul_one, Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
      exact abs_le_max_abs_abs g1 g2
    -- `(F_τ − F_c) z`
    have k2 : |((Fτ - Fcr) *ᵥ z) l| ≤ toReal ((Interval.point (mulVecUp Fr v)).materialise.sup l)
        := by
      rw [Interval.materialise_eq]
      change _ ≤ toReal (dotUp (Fr l) v)
      rw [show ((Fτ - Fcr) *ᵥ z) l = ∑ k, (Fτ - Fcr) l k * z k from rfl]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun k _ => ?_)
        (le_dotUp _ _))
      rw [abs_mul]
      have hk := hFcr l k
      exact mul_le_mul hk (hzv k) (abs_nonneg _) (le_trans (abs_nonneg _) hk)
    -- the scaled errors
    have hsl := hs l
    have k3 : |(lam • R + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + e₂) l|
        ≤ toReal (mulUp (s l) e) := by
      have hR' : |lam * R l| ≤ toReal st'.h * toReal (s l) := by
        rw [abs_mul, abs_of_nonneg hlam0]
        have := hR l
        have hhs := mul_nonneg hh' hsl.le
        nlinarith [abs_nonneg (R l)]
      -- `h' + γ h + ρ'` rounded up
      have a1 := add_le_addUp st'.h (mulUp γ st.h)
      have a2 := add_le_addUp (addUp st'.h (mulUp γ st.h)) st'.ρ
      have a3 := mul_le_mulUp γ st.h
      have a4 := mul_le_mulUp (s l) e
      have hesum : toReal st'.h + toReal γ * toReal st.h + toReal st'.ρ ≤ toReal e := by
        rw [he]; linarith
      have key := mul_le_mul_of_nonneg_left hesum hsl.le
      have := abs_add_le (lam * R l + (((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε) l)
        (e₂ l)
      have := abs_add_le (lam * R l) ((((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε) l)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hεl := hεb l
      have he₂l := he₂ l
      nlinarith
    -- the four parts against the box rounded up
    have a1 := add_le_addUp (st'.b l) (sumUp fun j => WG.magnitudeMat l j)
    have a2 := add_le_addUp (addUp (st'.b l) (sumUp fun j => WG.magnitudeMat l j))
      ((Interval.point (mulVecUp Fr v)).materialise.sup l)
    have a3 := add_le_addUp (addUp (addUp (st'.b l) (sumUp fun j => WG.magnitudeMat l j))
      ((Interval.point (mulVecUp Fr v)).materialise.sup l)) (mulUp (s l) e)
    have t1 := abs_add_le ((e₁ + (Fcr * Gr) *ᵥ b + (Fτ - Fcr) *ᵥ z) l)
      ((lam • R + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + e₂) l)
    have t2 := abs_add_le ((e₁ + (Fcr * Gr) *ᵥ b) l) (((Fτ - Fcr) *ᵥ z) l)
    have t3 := abs_add_le (e₁ l) (((Fcr * Gr) *ᵥ b) l)
    rw [heb]
    simp only [Pi.add_apply] at t1 t2 t3 k3 ⊢
    linarith [he₁ l]
  -- the point is the center plus the spans plus the box
  have S1 : ∑ j, b j • g₁ j = (1 / 2 : ℝ) • (Gr *ᵥ b + Gr' *ᵥ b) := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, hg₁]
    rw [show (Gr *ᵥ b) l = ∑ j, Gr l j * b j from rfl,
      show (Gr' *ᵥ b) l = ∑ j, Gr' l j * b j from rfl, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have S2 : ∑ j, (β * b j) • g₂ j = (β / 2) • (Gr *ᵥ b - Gr' *ᵥ b) := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hg₂]
    rw [show (Gr *ᵥ b) l = ∑ j, Gr l j * b j from rfl,
      show (Gr' *ᵥ b) l = ∑ j, Gr' l j * b j from rfl, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have S3 : g₃ = (1 / 2 : ℝ) • (cr - cr') := by
    funext l; simp only [hg₃, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; ring
  -- `F_τ z` about the center `F_c`
  have hFz : Fτ *ᵥ z = Fcr *ᵥ cr + (Fcr * Gr) *ᵥ b + (Fτ - Fcr) *ᵥ z := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    have : Fcr *ᵥ z = Fcr *ᵥ cr + Fcr *ᵥ (Gr *ᵥ b) := Matrix.mulVec_add _ _ _
    rw [← this]; abel
  have heq : (1 - lam) • z + lam • (z' + R) + Fτ *ᵥ z + gτ
      + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + (y₂ + e₁ + e₂)
      = ĉ + y₁ + y₂ + eb := by
    rw [hFz, hĉ, hy₁, heb, S1, S2, S3, hβ]
    simp only [z, z']
    module
  rw [heq]
  exact LinearSys.aux_ofBoxes hĉm hL hy₁m hy₂ hebm


-- =======================================  MAIN THEOREM  ======================================= --

omit [ToRat 𝕋] in
set_option maxHeartbeats 1000000 in -- the step is unfolded match by match
theorem LinearSys.verifyZonotopePassFloat_step (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {u₀ : Interval (Mat 𝕋 n 1)} {MU : Interval (Mat 𝕋 n p)}
    {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n p} (hM : Mr ∈ MU.toSet)
    (C : Mat 𝕋 q n) (specs : List (LinearSys.VerifySpecSet 𝕋 q)) {c₀ : Vec ℝ n} {G₀ : Mat ℝ n m}
    {t : ℝ} {st : LinearSys.VerifyZonoState 𝕋 n m}
    (hinv : sys.IsVerifyZonoInvariant (toRealVec s) c₀ G₀ (fun l => u0r l 0)
      ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) t st)
    (g : LinearSys.VerifyGridStep 𝕋) : -- --- CONCL ---
    ∀ r ∈ LinearSys.step_verifyZonoStepFloat sys.A s u₀ MU C specs st g, 0 < toReal g.Δt ∧
    sys.IsVerifyZonoInvariant (toRealVec s) c₀ G₀ (fun l => u0r l 0)
      ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (t + toReal g.Δt) r.2 ∧
    ∀ Y fl, r.1 = some (Y, fl) → fl = specs.map (LinearSys.verifySpecHoldsFloat Y) ∧
      ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal g.Δt →
      ∀ y ∈ sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (t + τ),
        toRealMat C *ᵥ (exp ((t + τ) • toRealMat sys.A) *ᵥ (c₀ + G₀ *ᵥ b)
          + Real.MatExp.expIntegral (toRealMat sys.A) (t + τ) *ᵥ (fun l => u0r l 0) + y)
          ∈ Y.toSet := by -- --- PROOF ---
  rintro ⟨o, st'⟩ h
  replace h : LinearSys.step_verifyZonoStepFloat sys.A s u₀ MU C specs st g = some (o, st') := h
  obtain ⟨ht, hh, hφ, hρ, hz, hΦ, hP⟩ := hinv
  set A := toRealMat sys.A with hA
  set u0v : Vec ℝ n := fun l => u0r l 0 with hu0v
  set V : Set (Vec ℝ n) := (fun β => Mr *ᵥ β) '' Set.Icc (-1) 1 with hV
  have hbdd : Bornology.IsBounded V :=
    (isCompact_Icc.image (Matrix.mulVecLin Mr).continuous_of_finiteDimensional).isBounded
  have hV0 : (0 : Vec ℝ n) ∈ V :=
    ⟨0, ⟨fun _ => by norm_num, fun _ => by norm_num⟩, Matrix.mulVec_zero _⟩
  -- a positive step, the exponential's ball, the input's boxes
  unfold LinearSys.step_verifyZonoStepFloat at h
  have hpos : ltStrict (FloatOps.zero : 𝕋) g.Δt = true := by
    by_contra hc
    rw [if_pos (by simpa using hc)] at h
    simp at h
  rw [if_neg (by simpa using hpos)] at h
  have hΔt : 0 < toReal g.Δt := by
    have := toReal_lt_of_ltStrict hpos
    rwa [toReal_zero] at this
  split at h
  · simp at h
  rename_i D r hDr
  have hD := MatExp.norm_scaleConj_exp_sub_le_expBallFloat sys.A hs hΔt.le (D, r)
    (Option.mem_def.mpr hDr)
  split at h
  · simp at h
  rename_i I gu hIg
  obtain ⟨hfacts, hgu⟩ := LinearSys.aux_inputBoxes_mem sys hs hΔt hu hM hIg
  -- the carried zonotope and the varying input at `t + Δt`
  set E := exp (toReal g.Δt • A) with hE
  set wr : Vec ℝ n := Real.MatExp.expIntegral A (toReal g.Δt) *ᵥ u0v with hwr
  have hw : ∀ l, toReal (I.w.inf l 0) ≤ wr l ∧ wr l ≤ toReal (I.w.sup l 0) :=
    fun l => (Interval.mem_mat_iff.mp hfacts.1) l 0
  obtain ⟨hh', hφ', -, -, -, hres, hΦ'⟩ := LinearSys.aux_carry hs hD hw st hh hφ
  obtain ⟨hρ', hP'⟩ := LinearSys.aux_inputStep sys hs hΔt hfacts g.budget st ht hφ hρ hΦ hP
  -- the state at `t + Δt`
  set inp := LinearSys.step_verifyZonoInputStepFloat s I g.budget st with hinp
  set stc := LinearSys.step_verifyZonoCarryFloat s D r I.w st with hstc
  set st₁ : LinearSys.VerifyZonoState 𝕋 n m := { stc with P := inp.1, b := inp.2.1, ρ := inp.2.2 }
    with hst₁
  -- `x(t + τ) = e^{τA} x(t) + (∫₀^τ e^{σA} dσ) u₀`
  have hflow : ∀ τ : ℝ, 0 ≤ τ → ∀ b : Fin m → ℝ,
      exp ((t + τ) • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A (t + τ) *ᵥ u0v
        = exp (τ • A) *ᵥ (exp (t • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A t *ᵥ u0v)
          + Real.MatExp.expIntegral A τ *ᵥ u0v := by
    intro τ hτ b
    rw [Real.MatExp.expIntegral_add_mulVec A u0v ht hτ, Matrix.mulVec_add,
      add_smul, add_comm (t • A), Matrix.exp_add_of_commute _ _
        (((Commute.refl A).smul_left τ).smul_right t),
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_add]
    simp only [Matrix.mulVec_add]
    abel
  -- the invariant at `t + Δt`: the carried zonotope, `e^{A(t + Δt)}`, the input
  have hinv' : sys.IsVerifyZonoInvariant (toRealVec s) c₀ G₀ u0v V (t + toReal g.Δt) st₁ := by
    refine ⟨by linarith, hh', hφ', hρ', fun b hb i => ?_, fun a ha x hx i => ?_, hP'⟩
    · rw [hflow _ hΔt.le b]
      set ε := exp (t • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A t *ᵥ u0v
        - (toRealVec st.c + toRealMat st.G *ᵥ b) with hε
      have := hres b hb ε (hz b hb) i
      rw [show toRealVec st.c + toRealMat st.G *ᵥ b + ε
        = exp (t • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A t *ᵥ u0v by
        rw [hε]; abel] at this
      exact this
    · have := hΦ' (exp (t • A)) hΦ a ha x hx i
      rwa [show E * exp (t • A) = exp ((t + toReal g.Δt) • A) by
        rw [hE, ← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left _).smul_right t),
          ← add_smul, add_comm]] at this
  -- a step only propagated has no output
  by_cases hfull : g.full = true
  rotate_left
  · rw [if_pos (by simpa using hfull)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hΔt, hinv', fun Y fl hY => by simp at hY⟩
  rw [if_neg (by simpa using hfull)] at h
  split at h
  · simp at h
  rename_i Fp F hF
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨hΔt, hinv', fun Y fl hY => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hY
  obtain ⟨rfl, rfl⟩ := hY
  refine ⟨rfl, fun b hb τ hτ0 hτ1 y hy => ?_⟩
  -- the varying input at `t + τ` lies in its set at `t + Δt`
  have hy' := sys.inputReach_mono (S := ExactSet) (U := V) hbdd hV0 (by linarith)
    (by linarith : t + τ ≤ t + toReal g.Δt) hy
  obtain ⟨y₂, hy₂, e₁, e₂, he₁, he₂, rfl⟩ := hP' y hy'
  -- the decomposition of `x(t + τ)`
  set lam := τ / toReal g.Δt with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hτ0 hΔt.le
  have hlam1 : lam ≤ 1 := (div_le_one hΔt).mpr hτ1
  set Fτ := exp (τ • A) - 1 - lam • (E - 1) with hFτ
  -- `F_τ ∈ F` and `G_τ u₀ ∈ G u₀`, the correction matrices
  have hFτm : Fτ ∈ F.toSet :=
    MatExp.expDiff_mem_verifyCorrectionStateFloat sys.A hs hΔt (Fp, F) (Option.mem_def.mpr hF)
      τ hτ0 hτ1
  set gτ : Vec ℝ n := (Real.MatExp.expIntegral A τ
    - lam • Real.MatExp.expIntegral A (toReal g.Δt)) *ᵥ u0v with hgτ
  have hgτm : ∀ l, toReal (gu.inf l 0) ≤ gτ l ∧ gτ l ≤ toReal (gu.sup l 0) :=
    fun l => (Interval.mem_mat_iff.mp (hgu τ hτ0 hτ1)) l 0
  set z := toRealVec st.c + toRealMat st.G *ᵥ b with hzdef
  set z' := toRealVec st₁.c + toRealMat st₁.G *ᵥ b with hz'def
  set ε := exp (t • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A t *ᵥ u0v - z with hε
  set R := E *ᵥ (z + ε) + wr - z' with hR
  have hRb : ∀ k, |R k| ≤ toReal st₁.h * toReal (s k) := fun k => hres b hb ε (hz b hb) k
  have hmem := LinearSys.aux_interval hs st st₁ hh hh' hlam0 hlam1 hb (hz b hb) hRb hFτm hgτm
    hy₂ he₁ he₂
  -- `x(t + τ)` as the set's center, spans and box
  have heq : exp ((t + τ) • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A (t + τ) *ᵥ u0v
      + (y₂ + e₁ + e₂)
      = (1 - lam) • z + lam • (z' + R) + Fτ *ᵥ z + gτ
        + ((1 - lam) • (1 : Mat ℝ n n) + Fτ) *ᵥ ε + (y₂ + e₁ + e₂) := by
    rw [hflow τ hτ0 b]
    have hx : exp (t • A) *ᵥ (c₀ + G₀ *ᵥ b) + Real.MatExp.expIntegral A t *ᵥ u0v = z + ε := by
      rw [hε]; abel
    rw [hx, hR, hgτ, hFτ, hwr]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_add]
    module
  rw [heq]
  exact LinearSys.aux_map C hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
