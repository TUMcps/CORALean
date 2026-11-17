module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpLeWeighted
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadLeQuadBoundUp
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.EnergyGrowthFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfSumAbsLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaleConjExp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PsdCheckSound
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.Global.EuclideanNorm
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `MatExp.energyGrowthFloat` bounds the balanced growth of `e^{tA}` by `c e^{rt}`

The two certified matrices give `a xᵀx ≤ xᵀP̃x ≤ b xᵀx` and `xᵀP̃Ãx ≤ r xᵀP̃x` for the real
`Ã = Σ⁻¹AΣ` within its two roundings, so `‖e^{tÃ}x‖₂ ≤ √(b/a) e^{rt} ‖x‖₂`
(`Krylov.norm_exp_le_weighted`), and `e^{tÃ} = Σ⁻¹e^{tA}Σ` (`MatExp.scaleConj_exp`). A row of
`S⁻¹e^{tA}S` is `σᵢ/sᵢ` times that of `e^{tÃ}` weighted by `sⱼ/σⱼ`; its absolute sum is the row
of `e^{tÃ}` against the signed weights, at most `√(b/a) e^{rt}` times their length.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `r` – float rate

## Hypotheses
* `hs` – the scales are positive

## Conclusion
* an accepted factor `c` bounds the balanced norm of `e^{tA}` by `c e^{rt}` at every `t ≥ 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row of `S⁻¹ E S` is `σᵢ/sᵢ` times the row of `F = Σ⁻¹ E Σ` weighted by `sⱼ/σⱼ`: a 2-norm bound
`K` of `F` bounds it by `m K w`. -/
private theorem MatExp.aux_norm_le (E : Mat ℝ n n) {s σ : Vec ℝ n} (hs : ∀ i, 0 < s i)
    (hσ : ∀ i, 0 < σ i) {K m w : ℝ} (hK0 : 0 ≤ K) (hm0 : 0 ≤ m)
    (hK : ∀ x, ‖Real.MatExp.scaleConj σ E *ᵥ x‖₂ ≤ K * ‖x‖₂) (hm : ∀ i, σ i / s i ≤ m)
    (hw : Real.sqrt (∑ j, (s j / σ j) ^ 2) ≤ w) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj s E‖ ≤ m * K * w := by -- --- PROOF ---
  set F := Real.MatExp.scaleConj σ E with hF
  have hent : ∀ i j, Real.MatExp.scaleConj s E i j = σ i / s i * F i j * (s j / σ j) := by
    intro i j
    simp only [hF, Real.MatExp.scaleConj, mul_diagonal, diagonal_mul]
    field_simp [(hs i).ne', (hσ i).ne', (hσ j).ne']
  -- row by row
  have hw0 : 0 ≤ w := (Real.sqrt_nonneg _).trans hw
  refine Real.MatExp.norm_le_of_sum_abs_le _ (by positivity) fun i => ?_
  -- the signed weights of row `i`
  set x : Vec ℝ n := fun j => if 0 ≤ F i j then s j / σ j else -(s j / σ j) with hx
  have hrow : ∑ j, |Real.MatExp.scaleConj s E i j| = σ i / s i * (F *ᵥ x) i := by
    rw [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : 0 < σ i / s i := div_pos (hσ i) (hs i)
    have h2 : 0 < s j / σ j := div_pos (hs j) (hσ j)
    rw [hent, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2, hx]
    dsimp only
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  -- the weights' length, and the row against them
  have hxn : ‖x‖₂ = Real.sqrt (∑ j, (s j / σ j) ^ 2) := by
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => ?_)
    simp only [hx]
    split_ifs <;> ring
  have hFx : (F *ᵥ x) i ≤ K * w :=
    (le_abs_self _).trans ((abs_le_norm₂ _ i).trans ((hK x).trans
      (mul_le_mul_of_nonneg_left (hxn ▸ hw) hK0)))
  have hc0 : 0 ≤ (F *ᵥ x) i := by
    have h := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      abs_nonneg (Real.MatExp.scaleConj s E i j)
    rw [hrow] at h
    exact (mul_nonneg_iff_of_pos_left (div_pos (hσ i) (hs i))).mp h
  rw [hrow]
  calc σ i / s i * (F *ᵥ x) i ≤ m * (K * w) := mul_le_mul (hm i) hFx hc0 hm0
    _ = m * K * w := by ring

/-- `2⁻ᵏ` is positive. -/
private theorem MatExp.aux_halfIter_pos (k : ℕ) : 0 < toReal (half^[k] (FloatOps.one : 𝕋)) := by
  induction k with
  | zero => simp [toReal_one]
  | succ k ih => rw [Function.iterate_succ_apply', toReal_half]; exact half_pos ih


/-- The shift's check: `a xᵀx ≤ xᵀP̃x` with `0 < a`. -/
private theorem MatExp.aux_shift {h : ℕ} {Pt : Mat 𝕋 n n} {a : 𝕋}
    (hsym : (toRealMat Pt)ᵀ = toRealMat Pt)
    (ha : a ∈ MatExp.step_energyShiftFloat h Pt) : -- --- CONCL ---
    0 < toReal a ∧
      ∀ x : Vec ℝ n, toReal a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (toRealMat Pt *ᵥ x) := by -- --- PROOF ---
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some (Option.mem_def.mp ha)
  dsimp only at hk
  split_ifs at hk with hX
  cases hk
  -- `P̃ - aI` within its two roundings, symmetric
  unfold MatExp.step_energyPsdFloat at hX
  have hpsd := Ellipsoid.posSemidef_of_psdCheck hX
    (Xr := toRealMat Pt - toReal (half^[k] (FloatOps.one : 𝕋)) • (1 : Mat ℝ n n))
    (fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, toRealMat]
      split_ifs with hij
      · subst hij
        exact ⟨by linarith [subDown_le_sub (Pt i i) (half^[k] (FloatOps.one : 𝕋))],
          by linarith [sub_le_subUp (Pt i i) (half^[k] (FloatOps.one : 𝕋))]⟩
      · simp)
    (fun i j => by
      have h := congrFun (congrFun hsym j) i
      simp only [Matrix.transpose_apply] at h
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, h, eq_comm (a := i)])
  -- its quadratic form
  refine ⟨MatExp.aux_halfIter_pos k, fun x => ?_⟩
  have h := hpsd.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  linarith

/-- The rate's check: `xᵀP̃Ãx ≤ r xᵀP̃x` for every `Ã` within `At`. -/
private theorem MatExp.aux_rate {h : ℕ} {Pt : Mat 𝕋 n n} {At : Interval (Mat 𝕋 n n)} {r : 𝕋}
    {Ar : Mat ℝ n n} (hsym : (toRealMat Pt)ᵀ = toRealMat Pt) (hAr : Ar ∈ At.toSet)
    (hr : MatExp.step_energyRateFloat h Pt At r = true) (x : Vec ℝ n) : -- --- CONCL ---
    x ⬝ᵥ (toRealMat Pt *ᵥ (Ar *ᵥ x)) ≤ toReal r * (x ⬝ᵥ (toRealMat Pt *ᵥ x)) := by -- --- PROOF ---
  unfold MatExp.step_energyRateFloat MatExp.step_energyPsdFloat at hr
  simp only [Interval.materialiseMat_eq] at hr
  set M := Interval.matMul (Interval.point Pt) At with hM
  set Pr := toRealMat Pt with hPr
  have hPA : Pr * Ar ∈ M.toSet :=
    Interval.matMul_outer _ _ (Interval.mem_mat_iff.mpr fun i j => ⟨le_refl _, le_refl _⟩) hAr
  have hPA' := Interval.mem_mat_iff.mp hPA
  -- `Z = 2rP̃ - P̃Ã - (P̃Ã)ᵀ` within its two roundings, symmetric
  have hP : ∀ i j, Pr j i = Pr i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym i) j
  have hpsd := Ellipsoid.posSemidef_of_psdCheck hr
    (Xr := (2 * toReal r) • Pr - Pr * Ar - (Pr * Ar)ᵀ)
    (fun i j => by
      dsimp only
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
      have e1 := mulDown_le_mul r (Pt i j)
      have e2 := mul_le_mulUp r (Pt i j)
      have e3 := addDown_le_add (mulDown r (Pt i j)) (mulDown r (Pt i j))
      have e4 := add_le_addUp (mulUp r (Pt i j)) (mulUp r (Pt i j))
      -- the rounded ends, and `P̃Ã`'s bracket
      have e5 := subDown_le_sub (addDown (mulDown r (Pt i j)) (mulDown r (Pt i j))) (M.sup i j)
      have e6 := subDown_le_sub (subDown (addDown (mulDown r (Pt i j)) (mulDown r (Pt i j)))
        (M.sup i j)) (M.sup j i)
      have e7 := sub_le_subUp (addUp (mulUp r (Pt i j)) (mulUp r (Pt i j))) (M.inf i j)
      have e8 := sub_le_subUp (subUp (addUp (mulUp r (Pt i j)) (mulUp r (Pt i j)))
        (M.inf i j)) (M.inf j i)
      obtain ⟨f1, f2⟩ := hPA' i j
      obtain ⟨f3, f4⟩ := hPA' j i
      have g : Pr i j = toReal (Pt i j) := rfl
      rw [g]
      constructor <;> linarith)
    (fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, hP i j]
      ring)
  -- `0 ≤ xᵀZx = 2r xᵀP̃x - 2 xᵀP̃Ãx`
  have h := hpsd.dotProduct_mulVec_nonneg x
  have hT : x ⬝ᵥ ((Pr * Ar)ᵀ *ᵥ x) = x ⬝ᵥ ((Pr * Ar) *ᵥ x) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, hT, ← Matrix.mulVec_mulVec] at h
  linarith

/-- The checks' content: `c e^{rt}` bounds the balanced growth. -/
private theorem MatExp.aux_core (A : Mat 𝕋 n n) {s σ : Vec 𝕋 n} {At : Interval (Mat 𝕋 n n)}
    {h : ℕ} {Pt : Mat 𝕋 n n} {r a : 𝕋} (hs : ∀ i, 0 < toReal (s i)) (hσ : ∀ i, 0 < toReal (σ i))
    (hn : 0 < n) (hAt : Real.MatExp.scaleConj (toRealVec σ) (toRealMat A) ∈ At.toSet)
    (hsym : (toRealMat Pt)ᵀ = toRealMat Pt) (ha : a ∈ MatExp.step_energyShiftFloat h Pt)
    (hr : MatExp.step_energyRateFloat h Pt At r = true) {t : ℝ} (ht : 0 ≤ t) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤
      toReal (MatExp.step_energyFactorFloat s σ Pt a) *
        Real.exp (t * toReal r) := by -- --- PROOF ---
  set Ar := Real.MatExp.scaleConj (toRealVec σ) (toRealMat A) with hAr
  set b := Krylov.quadBoundUp Pt with hb
  obtain ⟨ha0, hlow⟩ := MatExp.aux_shift hsym ha
  have hup := Krylov.quad_le_quadBoundUp Pt
  -- `a ≤ b` at a unit vector
  have hab : toReal a ≤ toReal b := by
    have h1 := hlow (Pi.single ⟨0, hn⟩ 1)
    have h2 := hup (Pi.single ⟨0, hn⟩ 1)
    have h3 : (Pi.single ⟨0, hn⟩ (1 : ℝ) : Vec ℝ n) ⬝ᵥ Pi.single ⟨0, hn⟩ 1 = 1 := by
      simp [dotProduct, Pi.single_apply]
    rw [h3] at h1 h2
    linarith
  -- the 2-norm growth of `e^{tÃ} = Σ⁻¹ e^{tA} Σ`
  have hσ0 : ∀ i, toRealVec σ i ≠ 0 := fun i => (hσ i).ne'
  have hconj : exp (t • Ar) = Real.MatExp.scaleConj (toRealVec σ) (exp (t • toRealMat A)) := by
    rw [Real.MatExp.scaleConj_exp hσ0, hAr]
    simp [Real.MatExp.scaleConj]
  set K := Real.sqrt (toReal b / toReal a) * Real.exp (toReal r * t) with hK
  have hKx : ∀ x, ‖Real.MatExp.scaleConj (toRealVec σ) (exp (t • toRealMat A)) *ᵥ x‖₂ ≤
      K * ‖x‖₂ := fun x => by
    rw [← hconj]
    exact Krylov.norm_exp_le_weighted Ar (toRealMat Pt) (toReal r) (toReal a) (toReal b) hsym
      (MatExp.aux_rate hsym hAt hr) hlow hup ha0 (ha0.le.trans hab) x ht
  -- the weights
  set mo := maximumOver fun i => divUp (σ i) (s i) with hmo
  set wf := sqrtUp 64 (sumUp fun j => let x := divUp (s j) (σ j); mulUp x x) with hwf
  have hm : ∀ i, toRealVec σ i / toRealVec s i ≤ toReal mo := fun i =>
    (div_le_divUp (σ i) (s i) (hs i)).trans (le_maximumOver (fun i => divUp (σ i) (s i)) i)
  have hm0 : 0 ≤ toReal mo := (div_pos (hσ ⟨0, hn⟩) (hs ⟨0, hn⟩)).le.trans (hm ⟨0, hn⟩)
  have hw : Real.sqrt (∑ j, (toRealVec s j / toRealVec σ j) ^ 2) ≤ toReal wf := by
    refine (Real.sqrt_le_sqrt ((Finset.sum_le_sum fun j _ => ?_).trans (sum_le_sumUp _))).trans
      (le_sqrtUp 64 _)
    have h1 := div_le_divUp (s j) (σ j) (hσ j)
    have h0 : 0 ≤ toRealVec s j / toRealVec σ j := (div_pos (hs j) (hσ j)).le
    have h2 := mul_le_mulUp (divUp (s j) (σ j)) (divUp (s j) (σ j))
    dsimp only
    change toReal (s j) / toReal (σ j) ≤ _ at h1
    change 0 ≤ toReal (s j) / toReal (σ j) at h0
    change (toReal (s j) / toReal (σ j)) ^ 2 ≤ _
    nlinarith
  have hw0 : 0 ≤ toReal wf := (Real.sqrt_nonneg _).trans hw
  have hK0 : 0 ≤ K := by positivity
  have hmain := MatExp.aux_norm_le (exp (t • toRealMat A)) hs hσ hK0 hm0 hKx hm hw
  -- `√(b/a) ≤ ⌈√⌉`, then the two rounded-up products
  have hsq : Real.sqrt (toReal b / toReal a) ≤ toReal (sqrtUp 64 (divUp b a)) :=
    (Real.sqrt_le_sqrt (div_le_divUp b a ha0)).trans (le_sqrtUp 64 _)
  have hc1 := mul_le_mulUp (sqrtUp 64 (divUp b a)) mo
  have hc2 := mul_le_mulUp (mulUp (sqrtUp 64 (divUp b a)) mo) wf
  have he : 0 ≤ Real.exp (toReal r * t) := (Real.exp_pos _).le
  unfold MatExp.step_energyFactorFloat
  rw [← hb, mul_comm t]
  refine hmain.trans ?_
  rw [hK]
  calc toReal mo * (Real.sqrt (toReal b / toReal a) * Real.exp (toReal r * t)) * toReal wf
      ≤ toReal mo * (toReal (sqrtUp 64 (divUp b a)) * Real.exp (toReal r * t)) * toReal wf := by
        gcongr
    _ = toReal (sqrtUp 64 (divUp b a)) * toReal mo * toReal wf * Real.exp (toReal r * t) := by
        ring
    _ ≤ _ := by
        gcongr
        exact (mul_le_mul_of_nonneg_right hc1 hw0).trans hc2


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_scaleConj_exp_le_energyGrowthFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n} (r : 𝕋)
    (hs : ∀ i, 0 < toReal (s i)) : -- --- CONCL ---
    ∀ c ∈ MatExp.energyGrowthFloat A s r, ∀ t : ℝ, 0 ≤ t →
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤
        toReal c * Real.exp (t * toReal r) := by -- --- PROOF ---
  intro c hc t ht
  rw [Option.mem_def] at hc
  unfold MatExp.energyGrowthFloat at hc
  rcases hP : MatExp.energyWeightFloat A r with _ | ⟨h, P⟩
  · simp [hP] at hc
  rw [hP] at hc
  simp only [Option.bind_eq_bind, Option.bind_some, Interval.materialise_eq,
    Interval.materialiseMat_eq, Interval.point] at hc
  split_ifs at hc with hchk hr
  on_goal 2 => simp at hc
  obtain ⟨a, ha, hc⟩ := Option.bind_eq_some_iff.mp hc
  simp only [Option.some.injEq] at hc
  subst hc
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const] at hchk
  obtain ⟨hn, hchk⟩ := hchk
  set σ : Vec 𝕋 n := fun i => MatExp.step_energyScaleFloat 64 (P i i) FloatOps.one with hσd
  have hσ : ∀ i, 0 < toReal (σ i) := fun i => by
    have h := toReal_lt_of_ltStrict (hchk i).1
    rwa [toReal_zero] at h
  -- `Ã` within its two roundings
  refine MatExp.aux_core A (σ := σ) hs hσ hn (Interval.mem_mat_iff.mpr fun i j => ?_) ?_
    (Option.mem_def.mpr ha) hr ht
  · have happ : Real.MatExp.scaleConj (toRealVec σ) (toRealMat A) i j =
        toReal (A i j) * toReal (σ j) / toReal (σ i) := by
      simp [Real.MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul, toRealVec,
        toRealMat]
      ring
    rw [happ]
    exact ⟨(divDown_le_div _ _ (hσ i)).trans
        (div_le_div_of_nonneg_right (mulDown_le_mul _ _) (hσ i).le),
      (div_le_div_of_nonneg_right (mul_le_mulUp _ _) (hσ i).le).trans (div_le_divUp _ _ (hσ i))⟩
  -- `P̃` symmetric
  · ext i j
    exact le_antisymm (toReal_le_of_le ((hchk j).2 i)) (toReal_le_of_le ((hchk i).2 j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
