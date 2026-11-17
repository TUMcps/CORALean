module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaleConjExp
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.Basic
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfSumAbsLe
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `MatExp.expBallFloat` encloses `e^{AΔt}` in the balanced norm

With `h = Δt / 2^σ` (the halvings are exact), the Taylor sum of order `K` of `A h` lies in the
box `T` (`MatExp.expTaylor_mem_expIntervalTaylor`), and the series' tail in balanced coordinates
is at most the float remainder bound at `ν h ≥ ‖S⁻¹ A h S‖`, `ν h ≤ 4` and `K ≥ 6`
(`norm_exp_sub_expTaylor_le` at `S⁻¹ A h S`, which commutes with the exponential and the
series); so `e^{Ah}` is within `r₀` of `T`'s upper end. A squaring keeps the invariant:
`E² − D̃'` is `E(E − D̃) + (E − D̃)D̃` plus the rounding of `D̃ D̃`, whose balanced norms are at
most `(p + r) r`, `r p` and the box's width. After `σ` squarings `E = e^{2^σ h A} = e^{AΔt}`.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `Δt` – float step length

## Hypotheses
* `hs` – the scales are positive
* `hΔt` – the step length is nonnegative

## Conclusion
* every result `(D̃, r)` has `e^{AΔt}` within `r` of `D̃` in the balanced norm
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

/-- The similarity is multiplicative. -/
private theorem MatExp.aux_scaleConj_mul {s : Fin n → ℝ} (hs : ∀ i, s i ≠ 0)
    (M N : Mat ℝ n n) : -- --- CONCL ---
    Real.MatExp.scaleConj s (M * N)
      = Real.MatExp.scaleConj s M * Real.MatExp.scaleConj s N := by -- --- PROOF ---
  have h1 : diagonal s * diagonal (fun i => (s i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hs i))
  unfold Real.MatExp.scaleConj
  calc diagonal (fun i => (s i)⁻¹) * (M * N) * diagonal s
      = diagonal (fun i => (s i)⁻¹) * M * (diagonal s * diagonal (fun i => (s i)⁻¹)) * N
          * diagonal s := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The float scaled norm of `M` bounds the balanced norm of a matrix below `|M|`. -/
private theorem MatExp.aux_norm_scaleConj_le_step_scaledNormUpFloat {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) (M : Mat 𝕋 n n) {X : Mat ℝ n n}
    (hX : ∀ j k, |X j k| ≤ |toReal (M j k)|) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) X‖
      ≤ toReal (MatExp.step_scaledNormUpFloat s M) := by -- --- PROOF ---
  set f : Fin n → 𝕋 := fun j => sumUp fun k => divUp (mulUp (absolute (M j k)) (s k)) (s j)
    with hf
  have hnn : 0 ≤ toReal (MatExp.step_scaledNormUpFloat s M) := by
    unfold MatExp.step_scaledNormUpFloat; rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  refine Real.MatExp.norm_le_of_sum_abs_le _ hnn fun j => ?_
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
  unfold MatExp.step_scaledNormUpFloat; rw [toReal_maximum]; exact le_max_right _ _


/-- `σ` halvings divide by `2^σ`, exactly. -/
private theorem MatExp.aux_toReal_half_iterate (x : 𝕋) (σ : ℕ) :
    toReal (half^[σ] x) = toReal x / 2 ^ σ := by
  induction σ with
  | zero => simp
  | succ σ ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ, div_div]

/-- The similarity commutes with subtraction. -/
private theorem MatExp.aux_scaleConj_sub (s : Fin n → ℝ) (M N : Mat ℝ n n) :
    Real.MatExp.scaleConj s (M - N)
      = Real.MatExp.scaleConj s M - Real.MatExp.scaleConj s N := by
  simp only [Real.MatExp.scaleConj, Matrix.mul_sub, Matrix.sub_mul]

/-- The similarity is additive. -/
private theorem MatExp.aux_scaleConj_add (s : Fin n → ℝ) (M N : Mat ℝ n n) :
    Real.MatExp.scaleConj s (M + N)
      = Real.MatExp.scaleConj s M + Real.MatExp.scaleConj s N := by
  simp only [Real.MatExp.scaleConj, Matrix.mul_add, Matrix.add_mul]

/-- The similarity commutes with scaling. -/
private theorem MatExp.aux_scaleConj_smul (s : Fin n → ℝ) (c : ℝ) (M : Mat ℝ n n) :
    Real.MatExp.scaleConj s (c • M) = c • Real.MatExp.scaleConj s M := by
  simp only [Real.MatExp.scaleConj, Matrix.mul_smul, Matrix.smul_mul]

/-- The similarity of a power is the power of the similarity. -/
private theorem MatExp.aux_scaleConj_pow {s : Fin n → ℝ} (hs : ∀ i, s i ≠ 0) (M : Mat ℝ n n)
    (i : ℕ) : -- --- CONCL ---
    Real.MatExp.scaleConj s (M ^ i) = Real.MatExp.scaleConj s M ^ i := by -- --- PROOF ---
  induction i with
  | zero =>
    simp only [pow_zero, Real.MatExp.scaleConj, diagonal_mul_diagonal,
      ← diagonal_one]
    exact congrArg diagonal (funext fun i => by rw [mul_one]; exact inv_mul_cancel₀ (hs i))
  | succ i ih => rw [pow_succ, MatExp.aux_scaleConj_mul hs, ih, pow_succ]

/-- The similarity of the Taylor sum is the Taylor sum of the similarity. -/
private theorem MatExp.aux_scaleConj_expTaylor {s : Fin n → ℝ} (hs : ∀ i, s i ≠ 0)
    (X : Mat ℝ n n) (K : ℕ) : -- --- CONCL ---
    Real.MatExp.scaleConj s (Real.MatExp.expTaylor X K)
      = Real.MatExp.expTaylor (Real.MatExp.scaleConj s X) K := by -- --- PROOF ---
  simp only [Real.MatExp.expTaylor]
  rw [show Real.MatExp.scaleConj s (∑ i ∈ Finset.range (K + 1), ((Nat.factorial i : ℝ)⁻¹) • X ^ i)
      = ∑ i ∈ Finset.range (K + 1), Real.MatExp.scaleConj s (((Nat.factorial i : ℝ)⁻¹) • X ^ i)
      by simp only [Real.MatExp.scaleConj, Matrix.mul_sum, Matrix.sum_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MatExp.aux_scaleConj_smul, MatExp.aux_scaleConj_pow hs]

/-- A real matrix inside a box is within the box's width of its upper end, entry by entry. -/
private theorem MatExp.aux_abs_sub_sup_le {I : Interval (Mat 𝕋 n n)} {X : Mat ℝ n n}
    (hX : X ∈ I.toSet) (j k : Fin n) : -- --- CONCL ---
    |(X - toRealMat I.sup) j k| ≤ |toReal (subUp (I.sup j k) (I.inf j k))| := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (Interval.mem_mat_iff.mp hX) j k
  have h3 := sub_le_subUp (I.sup j k) (I.inf j k)
  rw [Matrix.sub_apply, abs_of_nonpos (by simp only [toRealMat]; linarith)]
  simp only [toRealMat]
  exact le_trans (by linarith) (le_abs_self _)

/-- One squaring keeps the radius. -/
private theorem MatExp.aux_square {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) {E : Mat ℝ n n}
    (B : Mat 𝕋 n n × 𝕋)
    (hB : ‖Real.MatExp.scaleConj (toRealVec s) (E - toRealMat B.1)‖ ≤ toReal B.2) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) (E * E - toRealMat (MatExp.step_expBallSquareFloat s B).1)‖
      ≤ toReal (MatExp.step_expBallSquareFloat s B).2 := by -- --- PROOF ---
  have hs0 : ∀ i, toRealVec s i ≠ 0 := fun i => (hs i).ne'
  set Q := (Interval.matMul (Interval.point B.1) (Interval.point B.1)).materialiseMat with hQ
  set P := toRealMat B.1 with hPdef
  set pf := MatExp.step_scaledNormUpFloat s B.1 with hpf
  set wf := MatExp.step_scaledNormUpFloat s fun j k => subUp (Q.sup j k) (Q.inf j k) with hwf
  -- the balanced norms of `D̃` and of the rounding of `D̃ D̃`
  have hPP : P * P ∈ Q.toSet := by
    rw [hQ, Interval.materialiseMat_eq]
    exact Interval.matMul_outer _ _ (Interval.mem_point B.1) (Interval.mem_point B.1)
  have hp := MatExp.aux_norm_scaleConj_le_step_scaledNormUpFloat hs B.1 (X := P) fun j k => le_rfl
  have hw := MatExp.aux_norm_scaleConj_le_step_scaledNormUpFloat hs
    (fun j k => subUp (Q.sup j k) (Q.inf j k)) (X := P * P - toRealMat Q.sup)
    (MatExp.aux_abs_sub_sup_le hPP)
  have hr0 : 0 ≤ toReal B.2 := le_trans (norm_nonneg _) hB
  set p := toReal pf with hpdef
  set r := toReal B.2 with hrdef
  -- `E² − D̃' = E (E − D̃) + (E − D̃) D̃ + (D̃ D̃ − D̃')`
  have hsplit : E * E - toRealMat Q.sup
      = E * (E - P) + (E - P) * P + (P * P - toRealMat Q.sup) := by noncomm_ring
  have hE : ‖Real.MatExp.scaleConj (toRealVec s) E‖ ≤ p + r := by
    have : Real.MatExp.scaleConj (toRealVec s) E = Real.MatExp.scaleConj (toRealVec s) P
        + Real.MatExp.scaleConj (toRealVec s) (E - P) := by
      rw [MatExp.aux_scaleConj_sub]; abel
    rw [this]; exact le_trans (norm_add_le _ _) (add_le_add hp hB)
  have h1 : ‖Real.MatExp.scaleConj (toRealVec s) (E * (E - P))‖ ≤ (p + r) * r := by
    rw [MatExp.aux_scaleConj_mul hs0]
    exact le_trans (norm_mul_le _ _) (mul_le_mul hE hB (norm_nonneg _)
      (le_trans (norm_nonneg _) hE))
  have h2 : ‖Real.MatExp.scaleConj (toRealVec s) ((E - P) * P)‖ ≤ r * p := by
    rw [MatExp.aux_scaleConj_mul hs0]
    exact le_trans (norm_mul_le _ _) (mul_le_mul hB hp (norm_nonneg _) hr0)
  show ‖Real.MatExp.scaleConj (toRealVec s) (E * E - toRealMat Q.sup)‖ ≤ _
  rw [hsplit, MatExp.aux_scaleConj_add, MatExp.aux_scaleConj_add]
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) hw) ?_)
  -- the float radius `(2p + r) r + w`, each operation rounded up
  have ha1 := add_le_addUp pf pf
  have ha2 := add_le_addUp (addUp pf pf) B.2
  have hm := mul_le_mulUp (addUp (addUp pf pf) B.2) B.2
  have ha3 := add_le_addUp (mulUp (addUp (addUp pf pf) B.2) B.2) wf
  have hmono : (p + p + r) * r ≤ toReal (addUp (addUp pf pf) B.2) * r :=
    mul_le_mul_of_nonneg_right (by rw [hpdef, hrdef]; linarith) hr0
  have hgoal : (p + r) * r + r * p + toReal wf
      ≤ toReal (addUp (mulUp (addUp (addUp pf pf) B.2) B.2) wf) := by
    nlinarith [hm, ha3, hmono]
  refine le_trans (add_le_add (add_le_add h1 h2) le_rfl) hgoal


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_scaleConj_exp_sub_le_expBallFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 ≤ toReal Δt) : -- --- CONCL ---
    ∀ p ∈ MatExp.expBallFloat A s Δt,
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • toRealMat A) - toRealMat p.1)‖
        ≤ toReal p.2 := by -- --- PROOF ---
  rintro ⟨P, r⟩ hP
  replace hP : MatExp.expBallFloat A s Δt = some (P, r) := Option.mem_def.mp hP
  have hs0 : ∀ i, toRealVec s i ≠ 0 := fun i => (hs i).ne'
  unfold MatExp.expBallFloat at hP
  dsimp only at hP
  set ν := mulUp (MatExp.step_scaledNormUpFloat s A) Δt with hν
  rcases hσ : (List.range 1100).find? (fun σ => le (half^[σ] ν) (nsmulDown 4 one)) with _ | σ
  · rw [hσ] at hP
    simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hP
  rw [hσ] at hP
  simp only [Option.bind_eq_bind, Option.bind_some] at hP
  rcases hK : (List.range' 6 55).find?
      (fun K => le (MatExp.expRemainderBound (half^[σ] ν) K) (half^[80] one)) with _ | K
  · rw [hK] at hP
    simp only [Option.bind_none, reduceCtorEq] at hP
  rw [hK] at hP
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hP
  have hσt := List.find?_some hσ
  -- the halved step and the scaled matrix
  set h : ℝ := toReal Δt / 2 ^ σ with hhdef
  have hh : toReal (half^[σ] Δt) = h := MatExp.aux_toReal_half_iterate Δt σ
  have hh0 : 0 ≤ h := div_nonneg hΔt (by positivity)
  set X : Mat ℝ n n := h • toRealMat A with hXdef
  set T := MatExp.expIntervalTaylor (Interval.smul (half^[σ] Δt) (half^[σ] Δt)
    (Interval.point A)) K with hTdef
  have hX : X ∈ (Interval.smul (half^[σ] Δt) (half^[σ] Δt) (Interval.point A)).toSet :=
    Interval.smul_outer (le_of_eq hh) (le_of_eq hh.symm) _ (Interval.mem_point A)
  have hT : Real.MatExp.expTaylor X K ∈ T.toSet := MatExp.expTaylor_mem_expIntervalTaylor _ hX K
  -- `‖S⁻¹ X S‖ ≤ ν / 2^σ ≤ 4`, and the order at least `6`
  have hnA := MatExp.aux_norm_scaleConj_le_step_scaledNormUpFloat hs A (X := toRealMat A)
    fun _ _ => le_rfl
  have hnX : ‖Real.MatExp.scaleConj (toRealVec s) X‖ ≤ toReal (half^[σ] ν) := by
    rw [MatExp.aux_scaleConj_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0,
      MatExp.aux_toReal_half_iterate, hhdef, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hnA hΔt
  have hnn : 0 ≤ toReal (half^[σ] ν) := le_trans (norm_nonneg _) hnX
  -- the halvings stopped at `ν / 2^σ ≤ 4`, the order search at `K ≥ 6`
  have hfour : toReal (half^[σ] ν) ≤ 4 := by
    have h1 := toReal_le_of_le hσt
    have h2 := nsmulDown_le 4 (one : 𝕋)
    rw [toReal_one] at h2
    push_cast at h2
    linarith
  have hK6 : (6 : ℝ) ≤ K := by
    have := List.mem_of_find?_eq_some hK
    rw [List.mem_range'_1] at this
    exact_mod_cast this.1
  have hε : toReal (half^[σ] ν) / ((K : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the tail of the series past the order `K`
  have hhalf : toReal (half^[σ] ν) / ((K : ℝ) + 2) < 1 := by linarith
  have hε' : ‖Real.MatExp.scaleConj (toRealVec s) X‖ / ((K : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right hnX (by positivity)) hhalf
  have hτ := MatExp.expRemainderBound_le K hnX hnn hε
  have hreal := Real.norm_exp_sub_expTaylor_le (Real.MatExp.scaleConj (toRealVec s) X) K hε'
  -- the start: `e^{X}` within `r₀` of `T`'s upper end
  have hw := MatExp.aux_norm_scaleConj_le_step_scaledNormUpFloat hs
    (fun j k => subUp (T.sup j k) (T.inf j k)) (X := Real.MatExp.expTaylor X K - toRealMat T.sup)
    (MatExp.aux_abs_sub_sup_le hT)
  have h0 : ‖Real.MatExp.scaleConj (toRealVec s) (exp X - toRealMat T.sup)‖
      ≤ toReal (addUp (MatExp.expRemainderBound (half^[σ] ν) K)
          (MatExp.step_scaledNormUpFloat s fun j k => subUp (T.sup j k) (T.inf j k))) := by
    have hsplit : exp X - toRealMat T.sup
        = (exp X - Real.MatExp.expTaylor X K) + (Real.MatExp.expTaylor X K - toRealMat T.sup) := by
      abel
    rw [hsplit, MatExp.aux_scaleConj_add, MatExp.aux_scaleConj_sub, Real.MatExp.scaleConj_exp hs0,
      MatExp.aux_scaleConj_expTaylor hs0]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add (le_trans hreal hτ) hw) ?_)
    exact add_le_addUp _ _
  -- every squaring keeps the radius
  set B₀ : Mat 𝕋 n n × 𝕋 := (T.sup, addUp (MatExp.expRemainderBound (half^[σ] ν) K)
    (MatExp.step_scaledNormUpFloat s fun j k => subUp (T.sup j k) (T.inf j k))) with hB₀
  have hinv : ∀ j : ℕ, ‖Real.MatExp.scaleConj (toRealVec s)
      (exp (((2 : ℝ) ^ j) • X) - toRealMat ((MatExp.step_expBallSquareFloat s)^[j] B₀).1)‖
      ≤ toReal ((MatExp.step_expBallSquareFloat s)^[j] B₀).2 := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hexp : exp (((2 : ℝ) ^ (j + 1)) • X)
          = exp (((2 : ℝ) ^ j) • X) * exp (((2 : ℝ) ^ j) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, pow_succ]; ring_nf
      rw [hexp]
      exact MatExp.aux_square hs _ ih
  -- after `σ` squarings: `2^σ h = Δt`
  have hfin := hinv σ
  rw [hP] at hfin
  have hΔ : ((2 : ℝ) ^ σ) • X = toReal Δt • toRealMat A := by
    rw [hXdef, smul_smul, hhdef,
      show (2 : ℝ) ^ σ * (toReal Δt / 2 ^ σ) = toReal Δt by field_simp]
  rwa [hΔ] at hfin

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
