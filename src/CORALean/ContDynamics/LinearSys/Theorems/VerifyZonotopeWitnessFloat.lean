module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopeWitnessFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyInputSolutionFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `LinearSys.verifyZonotopeWitnessFloat` answering `true` is a falsification

The witness's state is `x(t) = e^{tA} x₀ + y`, `x₀ = c + G b` and `y` what the constant input
`u_c + G_U β` contributes (`LinearSys.expIntegral_mem_inputReach`). `e^{tA} x₀ = D x₀ +
(e^{tA} − D) x₀` with `D x₀` in its box and `|((e^{tA} − D) x₀)ᵢ| ≤ r ν sᵢ`
(`MatExp.norm_scaleConj_exp_sub_le_expBallFloat`); `y` lies in the input's box
(`LinearSys.verifyInputSolutionFloat_mem`). Every point of the box of `C x(t)` violates the
specification, so `C x(t)` does.

## Inputs
* `sys` – linear system, its `A` the system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `S` – float safe or unsafe set
* `t` – float time
* `b` – float coefficients of the initial point
* `β` – float coefficients of the input

## Hypotheses
* `h` – the witness holds

## Conclusion
* `t > 0`, and an initial point and an input's contribution whose output violates `S` at `t`
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] in
/-- A row sum of a matrix is at most its norm. -/
private theorem LinearSys.aux_rowSum_le_norm (N : Mat ℝ n n) (i : Fin n) : -- --- CONCL ---
    ∑ k, |N i k| ≤ ‖N‖ := by -- --- PROOF ---
  rw [Matrix.linfty_opNorm_def]
  have h : (∑ k, ‖N i k‖₊) ≤ Finset.univ.sup fun i => ∑ k, ‖N i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖N i k‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  rw [NNReal.coe_sum] at h'
  simpa [coe_nnnorm, Real.norm_eq_abs] using h'

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] in
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
    -- the row sum of the balanced matrix
    _ = (∑ k, |Real.MatExp.scaleConj s M i k|) * h * s i := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [happ, abs_div, abs_mul, abs_of_pos (hs k), abs_of_pos hsi]
        field_simp
    _ ≤ a * h * s i := by
        have := le_trans hrow hM
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hh) hsi.le

/-- `c + M v` lies in its box. -/
private theorem LinearSys.aux_point (c : Vec 𝕋 n) (M : Mat 𝕋 n m)
    (v : Vec 𝕋 m) : -- --- CONCL ---
    (fun i (_ : Fin 1) => (toRealVec c + toRealMat M *ᵥ toRealVec v) i)
      ∈ (LinearSys.step_verifyWitnessPointFloat c M v).toSet := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i _ => ⟨?_, ?_⟩ <;>
    simp only [LinearSys.step_verifyWitnessPointFloat, Pi.add_apply, toRealVec]
  · have := addDown_le_add (c i) (dotDown (M i) v)
    linarith [dotDown_le (M i) v, show (toRealMat M *ᵥ toRealVec v) i
      = ∑ k, toReal (M i k) * toReal (v k) from rfl]
  · have := add_le_addUp (c i) (dotUp (M i) v)
    linarith [le_dotUp (M i) v, show (toRealMat M *ᵥ toRealVec v) i
      = ∑ k, toReal (M i k) * toReal (v k) from rfl]

/-- `a'y` over a box is at most its float bound. -/
private theorem LinearSys.aux_dotUp (a lo hi : Vec 𝕋 q) {y : Vec ℝ q}
    (hy : ∀ i, toReal (lo i) ≤ y i ∧ y i ≤ toReal (hi i)) : -- --- CONCL ---
    toRealVec a ⬝ᵥ y
      ≤ toReal (LinearSys.step_verifyWitnessDotUpFloat a lo hi) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  obtain ⟨h1, h2⟩ := hy i
  rw [toReal_maximum]
  have a1 := mul_le_mulUp (a i) (lo i)
  have a2 := mul_le_mulUp (a i) (hi i)
  simp only [toRealVec]
  rcases le_total 0 (toReal (a i)) with ha | ha
  · exact le_trans (le_trans (mul_le_mul_of_nonneg_left h2 ha) a2) (le_max_right _ _)
  · exact le_trans (le_trans (mul_le_mul_of_nonpos_left h1 ha) a1) (le_max_left _ _)

/-- `M x` lies in a box that holds `M X` for the column `X` of `x`. -/
private theorem LinearSys.aux_mem_col {T : Interval (Mat 𝕋 q 1)} (M : Mat ℝ q n) (X : Mat ℝ n 1)
    (x : Vec ℝ n) (hX : ∀ i, X i 0 = x i) (hT : M * X ∈ T.toSet) : -- --- CONCL ---
    ∀ l, toReal (T.inf l 0) ≤ (M *ᵥ x) l ∧
      (M *ᵥ x) l ≤ toReal (T.sup l 0) := by -- --- PROOF ---
  intro l
  have h := (Interval.mem_mat_iff.mp hT) l 0
  have he : (M * X) l 0 = (M *ᵥ x) l := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  rwa [he] at h


-- =======================================  MAIN THEOREM  ======================================= --

set_option maxHeartbeats 1000000 in -- the witness is unfolded with its `let`s
theorem LinearSys.verifyZonotopeWitnessFloat_violated (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (S : LinearSys.VerifySpecSet 𝕋 q) (t : 𝕋) (b : Vec 𝕋 m) (β : Vec 𝕋 p)
    (h : LinearSys.verifyZonotopeWitnessFloat sys.A c G Bm uc GU C S t b β
      = true) : -- --- CONCL ---
    let U := (fun β => toRealMat Bm *ᵥ (toRealVec uc + toRealMat GU *ᵥ β)) '' Set.Icc (-1) 1
    0 < toReal t ∧ ∃ bb : Fin m → ℝ, (∀ j, |bb j| ≤ 1) ∧
    ∃ y ∈ sys.inputReach (S := ExactSet) U (toReal t),
      let x := exp (toReal t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ bb) + y
      (S.safe = true → ∃ ab ∈ S.rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ (toRealMat C *ᵥ x)) ∧
      (S.safe = false → ∀ ab ∈ S.rows, toRealVec ab.1 ⬝ᵥ (toRealMat C *ᵥ x) ≤ toReal ab.2)
    := by -- --- PROOF ---
  intro U
  unfold LinearSys.verifyZonotopeWitnessFloat at h
  dsimp only at h
  split at h
  rotate_left
  · simp at h
  rename_i D r I hball hsol
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨hb, hβ⟩, ht⟩, hs⟩, hspec⟩ := h
  set s := MatExp.balanceScalesFloat sys.A with hsdef
  have hs' : ∀ i, 0 < toReal (s i) := fun i => by
    have := toReal_lt_of_ltStrict (hs i); rwa [toReal_zero] at this
  have ht' : 0 < toReal t := by
    have := toReal_lt_of_ltStrict ht; rwa [toReal_zero] at this
  have hcube : ∀ {l : ℕ} (v : Vec 𝕋 l), (∀ j, le (absolute (v j)) one = true) →
      ∀ j, |toRealVec v j| ≤ 1 := fun v hv j => by
    have := toReal_le_of_le (hv j); rwa [toReal_absolute, toReal_one] at this
  -- the witness: the initial point and the input's contribution
  set bb := toRealVec b
  set ur := toRealVec uc + toRealMat GU *ᵥ toRealVec β with hur
  set v := toRealMat Bm *ᵥ ur with hv
  have hvU : v ∈ U := ⟨toRealVec β, ⟨fun j => (abs_le.mp (hcube β hβ j)).1,
    fun j => (abs_le.mp (hcube β hβ j)).2⟩, rfl⟩
  set y := Real.MatExp.expIntegral (toRealMat sys.A) (toReal t) *ᵥ v with hy
  have hyR : y ∈ sys.inputReach (S := ExactSet) U (toReal t) :=
    sys.expIntegral_mem_inputReach (S := ExactSet) ht'.le hvU
  refine ⟨ht', bb, hcube b hb, y, hyR, ?_⟩
  intro x
  -- the boxes of `x₀` and `B u`, and the input's solution
  set x₀ := toRealVec c + toRealMat G *ᵥ bb with hx₀
  have hX₀ := LinearSys.aux_point c G b
  have hU₀ : (fun i (_ : Fin 1) => v i) ∈ (Interval.matMul (Interval.point Bm)
      (LinearSys.step_verifyWitnessPointFloat uc GU β)).materialiseMat.toSet := by
    rw [Interval.materialiseMat_eq]
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact LinearSys.aux_mem_col (toRealMat Bm) (fun i _ => ur i) ur (fun _ => rfl)
      (Interval.matMul_outer _ _ (Interval.mem_point Bm) (LinearSys.aux_point uc GU β)) i
  have hw := (LinearSys.verifyInputSolutionFloat_mem sys hs' ht' hU₀
    (Mr := fun _ j => j.elim0) (Interval.mem_mat_iff.mpr fun _ j => j.elim0) I hsol).1
  have hwv := LinearSys.aux_mem_col _ (fun i _ => v i) v (fun _ => rfl) hw
  have hD := MatExp.norm_scaleConj_exp_sub_le_expBallFloat sys.A hs' ht'.le (D, r) hball
  have hDX := LinearSys.aux_mem_col
    (T := (Interval.matMul (Interval.point D) (LinearSys.step_verifyWitnessPointFloat c G b)
      ).materialiseMat) (toRealMat D) (fun i _ => x₀ i) x₀ (fun _ => rfl)
    (by rw [Interval.materialiseMat_eq]; exact Interval.matMul_outer _ _ (Interval.mem_point D) hX₀)
  -- `(e^{tA} − D) x₀` within `r ν s`
  set X₀ := LinearSys.step_verifyWitnessPointFloat c G b
  set ν := maximum FloatOps.zero (maximumOver fun i =>
    divUp (maximum (absolute (X₀.inf i 0)) (absolute (X₀.sup i 0))) (s i)) with hν
  have hν0 : 0 ≤ toReal ν := by rw [hν, toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hx₀ν : ∀ i, |x₀ i| ≤ toReal ν * toRealVec s i := by
    intro i
    obtain ⟨h1, h2⟩ := (Interval.mem_mat_iff.mp hX₀) i 0
    have hsi := hs' i
    -- `|x₀ᵢ|` within the magnitude of its box, then `ν sᵢ`
    have hm : |x₀ i| ≤ toReal (maximum (absolute (X₀.inf i 0)) (absolute (X₀.sup i 0))) := by
      rw [toReal_maximum, toReal_absolute, toReal_absolute]; exact abs_le_max_abs_abs h1 h2
    have hdiv := div_le_divUp (maximum (absolute (X₀.inf i 0)) (absolute (X₀.sup i 0))) (s i) hsi
    have hmax := le_maximumOver (fun i => divUp (maximum (absolute (X₀.inf i 0))
      (absolute (X₀.sup i 0))) (s i)) i
    have hνm : toReal (maximumOver fun i => divUp (maximum (absolute (X₀.inf i 0))
        (absolute (X₀.sup i 0))) (s i)) ≤ toReal ν := by
      rw [hν, toReal_maximum]; exact le_max_right _ _
    have := le_trans hdiv (le_trans hmax hνm)
    rw [div_le_iff₀ hsi] at this
    exact le_trans hm this
  have hr0 : 0 ≤ toReal r := le_trans (norm_nonneg _) hD
  have hE := fun i => LinearSys.aux_scaled hs' hD hν0 hx₀ν i
  -- the box of `x(t)`, then of `C x(t)`
  have hxe : x = toRealMat D *ᵥ x₀ + (exp (toReal t • toRealMat sys.A) - toRealMat D) *ᵥ x₀ + y
      := by simp only [x, Matrix.sub_mulVec]; abel
  have hXt : (fun i (_ : Fin 1) => x i) ∈ (⟨fun i _ => subDown (addDown
      ((Interval.matMul (Interval.point D) X₀).materialiseMat.inf i 0) (I.w.inf i 0))
      (mulUp (mulUp r ν) (s i)), fun i _ => addUp (addUp
      ((Interval.matMul (Interval.point D) X₀).materialiseMat.sup i 0) (I.w.sup i 0))
      (mulUp (mulUp r ν) (s i))⟩ : Interval (Mat 𝕋 n 1)).toSet := by
    refine Interval.mem_mat_iff.mpr fun i _ => ?_
    obtain ⟨d1, d2⟩ := hDX i
    obtain ⟨w1, w2⟩ := hwv i
    have e1 := mul_le_mulUp r ν
    have e2 := mul_le_mulUp (mulUp r ν) (s i)
    have hsi := (hs' i).le
    have e3 : toReal r * toReal ν * toReal (s i) ≤ toReal (mulUp (mulUp r ν) (s i)) :=
      le_trans (mul_le_mul_of_nonneg_right e1 hsi) e2
    have hEi := hE i
    -- the ends of the box, rounded outward
    have a1 := subDown_le_sub (addDown ((Interval.matMul (Interval.point D) X₀).materialiseMat.inf
      i 0) (I.w.inf i 0)) (mulUp (mulUp r ν) (s i))
    have a2 := addDown_le_add ((Interval.matMul (Interval.point D) X₀).materialiseMat.inf i 0)
      (I.w.inf i 0)
    have a3 := add_le_addUp (addUp ((Interval.matMul (Interval.point D) X₀).materialiseMat.sup
      i 0) (I.w.sup i 0)) (mulUp (mulUp r ν) (s i))
    have a4 := add_le_addUp ((Interval.matMul (Interval.point D) X₀).materialiseMat.sup i 0)
      (I.w.sup i 0)
    rw [abs_le] at hEi
    rw [hxe]
    simp only [Pi.add_apply]
    constructor <;> linarith [hEi.1, hEi.2]
  have hYb := LinearSys.aux_mem_col (T := (Interval.matMul (Interval.point C) _).materialiseMat)
    (toRealMat C) (fun i _ => x i) x (fun _ => rfl)
    (by rw [Interval.materialiseMat_eq]; exact Interval.matMul_outer _ _ (Interval.mem_point C) hXt)
  -- each row along the box
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · rw [hS, if_pos rfl, List.any_eq_true] at hspec
    obtain ⟨ab, hab, hlt⟩ := hspec
    refine ⟨ab, hab, ?_⟩
    have h1 := toReal_lt_of_ltStrict hlt
    rw [toReal_neg] at h1
    have h2 := LinearSys.aux_dotUp (-ab.1) _ _ hYb
    have hn : toRealVec (-ab.1) ⬝ᵥ (toRealMat C *ᵥ x) = -(toRealVec ab.1 ⬝ᵥ (toRealMat C *ᵥ x))
        := by
      simp only [dotProduct, toRealVec, Pi.neg_apply, toReal_neg', neg_mul,
        Finset.sum_neg_distrib]
    linarith
  · rw [hS] at hspec
    simp only [Bool.false_eq_true, if_false, List.all_eq_true] at hspec
    intro ab hab
    exact le_trans (LinearSys.aux_dotUp ab.1 _ _ hYb) (toReal_le_of_le (hspec ab hab))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
