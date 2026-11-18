module

public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifyKrylovWindows
public import CORALean.ContDynamics.LinearSys.Operations.VerifyKrylovBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfSumAbsLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DotProductLeOfMemInputReach
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `LinearSys.verifyKrylovBoundsFloat` bounds the support of the reachable set step by step

If the windows hold `w' e^{tA}` (`LinearSys.IsVerifyKrylovWindows`, on the grid `ratio Δt`), then
the bound of step `j` holds `w' (e^{tA}(c + G β) + y)` for every `t ∈ [jΔt, (j+1)Δt]`,
`β ∈ [-1, 1]^m` and `y` the input `u(s) ∈ u_c + G_U [-1, 1]^p` contributes by `t`
(`LinearSys.inputReach`). On a step of a window, `ψ(τ) = e^{τH}e₁` is
`(1 - θ) ψ_i + θ ψ_{i+1} + Φ ψ_i` with `Φ ∈ [F]` (`MatExp.expDiff_mem_verifyCorrectionStateFloat`),
`ψ_i` within `s E_i` of the iterate `ŷ_i` (`MatExp.norm_scaleConj_exp_sub_le_expBallFloat`), so
each vector `v` has `z(t)' v = W_v ψ + e' v` within its term plus `err ‖v‖₂`; the input's part is
`LinearSys.dotProduct_le_of_mem_inputReach` with the integrands of the steps so far.

## Inputs
* `sys` – linear system, its `A` the system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `w` – float direction
* `wins` – the windows
* `ratio` – steps of the pass per step of the windows
* `Δt` – float step size
* `N` – number of steps

## Hypotheses
* `hwin` – the windows hold `w' e^{tA}` on the grid `ratio Δt`

## Conclusion
* `N` bounds, the `j`-th above `w' x(t)` over step `j` for every initial point and input
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The interval dot product holds every dot product of its members. -/
private theorem LinearSys.aux_dot {k : ℕ} {a b c d : Vec 𝕋 k} {x y : Vec ℝ k}
    (hx : ∀ l, toReal (a l) ≤ x l ∧ x l ≤ toReal (b l))
    (hy : ∀ l, toReal (c l) ≤ y l ∧ y l ≤ toReal (d l)) : -- --- CONCL ---
    toReal (LinearSys.step_verifyKrylovDotFloat a b c d).1 ≤ x ⬝ᵥ y ∧
      x ⬝ᵥ y ≤ toReal (LinearSys.step_verifyKrylovDotFloat a b c d).2 := by -- --- PROOF ---
  have h := fun l => Interval.mul_between_corners (hx l).1 (hx l).2 (hy l).1 (hy l).2
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun l _ => (h l).1),
    le_trans (Finset.sum_le_sum fun l _ => (h l).2) (sum_le_sumUp _)⟩

/-- A row within `R` makes of a vector within `r E` at most `Σ |R_l| r_l` times `E`. -/
private theorem LinearSys.aux_mag {k : ℕ} (R : Interval (Vec 𝕋 k)) (r : Vec 𝕋 k) {x e : Vec ℝ k}
    {E : ℝ} (hE : 0 ≤ E) (hx : ∀ l, toReal (R.inf l) ≤ x l ∧ x l ≤ toReal (R.sup l))
    (he : ∀ l, |e l| ≤ toReal (r l) * E) : -- --- CONCL ---
    |x ⬝ᵥ e| ≤ toReal (LinearSys.step_verifyKrylovMagFloat R r) * E := by -- --- PROOF ---
  set M := fun l => maximum (absolute (R.inf l)) (absolute (R.sup l))
  have hM : ∀ l, |x l| ≤ toReal (M l) := fun l => by
    simp only [M, toReal_maximum, toReal_absolute]
    rcases le_total 0 (x l) with h | h
    · rw [abs_of_nonneg h]
      exact le_trans (le_trans (hx l).2 (le_abs_self _)) (le_max_right _ _)
    · rw [abs_of_nonpos h]
      exact le_trans (le_trans (neg_le_neg (hx l).1) (neg_le_abs _)) (le_max_left _ _)
-- termwise, `|x_l| ≤ M_l` and `|e_l| ≤ r_l E`
  calc |x ⬝ᵥ e| ≤ ∑ l, |x l| * |e l| := by
        unfold dotProduct
        exact le_trans (Finset.abs_sum_le_sum_abs _ _)
          (le_of_eq (Finset.sum_congr rfl fun l _ => abs_mul _ _))
    _ ≤ ∑ l, toReal (mulUp (M l) (r l)) * E := Finset.sum_le_sum fun l _ => by
        calc |x l| * |e l| ≤ toReal (M l) * (toReal (r l) * E) :=
              mul_le_mul (hM l) (he l) (abs_nonneg _) (le_trans (abs_nonneg _) (hM l))
          _ = toReal (M l) * toReal (r l) * E := by ring
          _ ≤ toReal (mulUp (M l) (r l)) * E :=
              mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) hE
    _ = (∑ l, toReal (mulUp (M l) (r l))) * E := (Finset.sum_mul _ _ _).symm
    _ ≤ toReal (LinearSys.step_verifyKrylovMagFloat R r) * E :=
        mul_le_mul_of_nonneg_right (sum_le_sumUp _) hE

/-- A vector's term bounds its row's value on the step (its value if `signed`, else its
magnitude): the convex combination of the ends within `a E'`, the curvature within `b E`. -/
private theorem LinearSys.aux_term {k : ℕ} (signed : Bool) (R : Interval (Vec 𝕋 k))
    (s g y y' : Vec 𝕋 k) (Fy : Interval (Vec 𝕋 k)) (E E' : 𝕋) {W ψ₀ ψ₁ f fe : Vec ℝ k} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hs : ∀ l, 0 ≤ toReal (s l)) (hE : 0 ≤ toReal E)
    (hEE : toReal E ≤ toReal E') (hW : ∀ l, toReal (R.inf l) ≤ W l ∧ W l ≤ toReal (R.sup l))
    (h₀ : ∀ l, |ψ₀ l - toReal (y l)| ≤ toReal (s l) * toReal E)
    (h₁ : ∀ l, |ψ₁ l - toReal (y' l)| ≤ toReal (s l) * toReal E')
    (hf : ∀ l, toReal (Fy.inf l) ≤ f l ∧ f l ≤ toReal (Fy.sup l))
    (hfe : ∀ l, |fe l| ≤ toReal (g l) * toReal E) : -- --- CONCL ---
    (if signed then W ⬝ᵥ ((1 - θ) • ψ₀ + θ • ψ₁ + (f + fe))
      else |W ⬝ᵥ ((1 - θ) • ψ₀ + θ • ψ₁ + (f + fe))|) ≤
      toReal (LinearSys.step_verifyKrylovTermFloat signed R s g y y' Fy E E') := by -- --- PROOF ---
  have hE' : 0 ≤ toReal E' := le_trans hE hEE
  set P := LinearSys.step_verifyKrylovDotFloat R.inf R.sup y y
  set C := LinearSys.step_verifyKrylovDotFloat R.inf R.sup y' y'
  set K := LinearSys.step_verifyKrylovDotFloat R.inf R.sup Fy.inf Fy.sup
  set a := LinearSys.step_verifyKrylovMagFloat R s
  set b := LinearSys.step_verifyKrylovMagFloat R g
  -- the two ends, each the iterate's row value within `a E'`
  have hP := LinearSys.aux_dot (y := toRealVec y) hW fun l => ⟨le_rfl, le_rfl⟩
  have hC := LinearSys.aux_dot (y := toRealVec y') hW fun l => ⟨le_rfl, le_rfl⟩
  have hK := LinearSys.aux_dot hW hf
  have ha₀ := LinearSys.aux_mag R s hE' hW (e := ψ₀ - toRealVec y) fun l =>
    le_trans (h₀ l) (mul_le_mul_of_nonneg_left hEE (hs l))
  have ha₁ := LinearSys.aux_mag R s hE' hW (e := ψ₁ - toRealVec y') fun l => h₁ l
  have hb := LinearSys.aux_mag R g hE hW hfe
  have hd₀ : W ⬝ᵥ ψ₀ = W ⬝ᵥ toRealVec y + W ⬝ᵥ (ψ₀ - toRealVec y) := by
    rw [dotProduct_sub]; ring
  have hd₁ : W ⬝ᵥ ψ₁ = W ⬝ᵥ toRealVec y' + W ⬝ᵥ (ψ₁ - toRealVec y') := by
    rw [dotProduct_sub]; ring
  have hval : W ⬝ᵥ ((1 - θ) • ψ₀ + θ • ψ₁ + (f + fe))
      = (1 - θ) * (W ⬝ᵥ ψ₀) + θ * (W ⬝ᵥ ψ₁) + W ⬝ᵥ f + W ⬝ᵥ fe := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  -- the range `[lo - ext, hi + ext]`
  set lo := addDown (minimum P.1 C.1) K.1
  set hi := addUp (maximum P.2 C.2) K.2
  set ext := addUp (mulUp a E') (mulUp b E)
  have hext : toReal a * toReal E' + toReal b * toReal E ≤ toReal ext :=
    le_trans (add_le_add (mul_le_mulUp _ _) (mul_le_mulUp _ _)) (add_le_addUp _ _)
  have hlo : toReal (minimum P.1 C.1) + toReal K.1 ≥ toReal lo := addDown_le_add _ _
  have hhi : toReal (maximum P.2 C.2) + toReal K.2 ≤ toReal hi := add_le_addUp _ _
  rw [toReal_minimum] at hlo
  rw [toReal_maximum] at hhi
  have hab := abs_le.mp ha₀
  have hab₁ := abs_le.mp ha₁
  have hbb := abs_le.mp hb
  -- the convex combination of the ends
  have hup : W ⬝ᵥ ((1 - θ) • ψ₀ + θ • ψ₁ + (f + fe)) ≤ toReal hi + toReal ext := by
    rw [hval]
    have e0 : W ⬝ᵥ ψ₀ ≤ max (toReal P.2) (toReal C.2) + toReal a * toReal E' := by
      rw [hd₀]; linarith [le_max_left (toReal P.2) (toReal C.2), hP.2]
    have e1 : W ⬝ᵥ ψ₁ ≤ max (toReal P.2) (toReal C.2) + toReal a * toReal E' := by
      rw [hd₁]; linarith [le_max_right (toReal P.2) (toReal C.2), hC.2]
    have hc : (1 - θ) * (W ⬝ᵥ ψ₀) + θ * (W ⬝ᵥ ψ₁) ≤
        max (toReal P.2) (toReal C.2) + toReal a * toReal E' := by
      have := add_le_add (mul_le_mul_of_nonneg_left e0 (by linarith : (0:ℝ) ≤ 1 - θ))
        (mul_le_mul_of_nonneg_left e1 hθ0)
      linarith
    linarith [hK.2, hbb.2]
-- and the convex combination from below
  have hdown : toReal lo - toReal ext ≤ W ⬝ᵥ ((1 - θ) • ψ₀ + θ • ψ₁ + (f + fe)) := by
    rw [hval]
    have e0 : min (toReal P.1) (toReal C.1) - toReal a * toReal E' ≤ W ⬝ᵥ ψ₀ := by
      rw [hd₀]; linarith [min_le_left (toReal P.1) (toReal C.1), hP.1]
    have e1 : min (toReal P.1) (toReal C.1) - toReal a * toReal E' ≤ W ⬝ᵥ ψ₁ := by
      rw [hd₁]; linarith [min_le_right (toReal P.1) (toReal C.1), hC.1]
    have hc : min (toReal P.1) (toReal C.1) - toReal a * toReal E' ≤
        (1 - θ) * (W ⬝ᵥ ψ₀) + θ * (W ⬝ᵥ ψ₁) := by
      have := add_le_add (mul_le_mul_of_nonneg_left e0 (by linarith : (0:ℝ) ≤ 1 - θ))
        (mul_le_mul_of_nonneg_left e1 hθ0)
      linarith
    linarith [hK.1, hbb.1]
  -- the term: the upper end, or the magnitude
  unfold LinearSys.step_verifyKrylovTermFloat
  cases signed with
  | true =>
    simp only [if_true]
    exact le_trans hup (add_le_addUp _ _)
  | false =>
    simp only [Bool.false_eq_true, if_false]
    refine le_trans ?_ (add_le_addUp _ _)
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have := neg_abs_le (toReal lo)
      linarith [le_max_left |toReal lo| |toReal hi|]
    · have := le_abs_self (toReal hi)
      linarith [le_max_right |toReal lo| |toReal hi|]

/-- A matrix whose balanced norm is at most `r` maps a vector within `s X` into one within
`s r X`, entry by entry. -/
private theorem LinearSys.aux_scaled_mulVec {k : ℕ} {s : Vec ℝ k} (hs : ∀ l, 0 < s l)
    (M : Mat ℝ k k) {r X : ℝ} (hM : ‖Real.MatExp.scaleConj s M‖ ≤ r) (hX : 0 ≤ X) {x : Vec ℝ k}
    (hx : ∀ l, |x l| ≤ s l * X) : -- --- CONCL ---
    ∀ l, |(M *ᵥ x) l| ≤ s l * (r * X) := by -- --- PROOF ---
  intro l
  set v : Vec ℝ k := fun j => x j / s j with hv
  have hvn : ‖v‖ ≤ X := (pi_norm_le_iff_of_nonneg hX).mpr fun j => by
    rw [Real.norm_eq_abs, hv, abs_div, abs_of_pos (hs j), div_le_iff₀ (hs j)]
    linarith [hx j]
  have hxv : x = diagonal s *ᵥ v := funext fun j => by
    rw [mulVec_diagonal, hv]; field_simp [(hs j).ne']
  have hC : (Real.MatExp.scaleConj s M *ᵥ v) l = (M *ᵥ x) l / s l := by
    rw [Real.MatExp.scaleConj, ← mulVec_mulVec, ← mulVec_mulVec, ← hxv, mulVec_diagonal]
    rw [div_eq_inv_mul]
  have hb : |(Real.MatExp.scaleConj s M *ᵥ v) l| ≤ r * X :=
    calc |(Real.MatExp.scaleConj s M *ᵥ v) l| ≤ ‖Real.MatExp.scaleConj s M *ᵥ v‖ :=
          (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l)
      _ ≤ ‖Real.MatExp.scaleConj s M‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ r * X := mul_le_mul hM hvn (norm_nonneg _) (le_trans (norm_nonneg _) hM)
  rw [hC, abs_div, abs_of_pos (hs l), div_le_iff₀ (hs l)] at hb
  linarith

/-- The balanced similarity is additive. -/
private theorem LinearSys.aux_scaleConj_add {k : ℕ} (s : Vec ℝ k) (M N : Mat ℝ k k) :
    Real.MatExp.scaleConj s (M + N) = Real.MatExp.scaleConj s M + Real.MatExp.scaleConj s N := by
  unfold Real.MatExp.scaleConj
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The float balanced norm of `D̃` bounds its real one. -/
private theorem LinearSys.aux_norm_le_nD {k : ℕ} {s : Vec 𝕋 k} (hs : ∀ l, 0 < toReal (s l))
    (D : Mat 𝕋 k k) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) (toRealMat D)‖ ≤ toReal (maximum FloatOps.zero (maximumOver
      fun l => sumUp fun j => divUp (mulUp (absolute (D l j)) (s j)) (s l))) := by -- --- PROOF ---
  set f : Fin k → 𝕋 := fun l => sumUp fun j => divUp (mulUp (absolute (D l j)) (s j)) (s l)
  have hnn : 0 ≤ toReal (maximum FloatOps.zero (maximumOver f)) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  refine Real.MatExp.norm_le_of_sum_abs_le _ hnn fun l => ?_
  have hrow : ∑ j, |Real.MatExp.scaleConj (toRealVec s) (toRealMat D) l j| ≤ toReal (f l) := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    have happ : Real.MatExp.scaleConj (toRealVec s) (toRealMat D) l j
        = toReal (D l j) * toReal (s j) / toReal (s l) := by
      simp [Real.MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul, toRealVec,
        toRealMat]; ring
    rw [happ, abs_div, abs_mul, abs_of_pos (hs j), abs_of_pos (hs l)]
    have h1 := mul_le_mulUp (absolute (D l j)) (s j)
    rw [toReal_absolute] at h1
    exact le_trans (div_le_div_of_nonneg_right h1 (hs l).le) (div_le_divUp _ _ (hs l))
  refine le_trans hrow (le_trans (le_maximumOver f l) ?_)
  rw [toReal_maximum]; exact le_max_right _ _

/-- What a window's setup at `Δt > 0` certifies: positive scales, the ball of `e^{HΔt}`, the norm
of its center, the correction matrix, and `g` the row magnitudes of `[F]`. -/
private theorem LinearSys.aux_setup (W : LinearSys.VerifyKrylovWindow 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {s : Vec 𝕋 W.k} {D : Mat 𝕋 W.k W.k} {rD nD : 𝕋}
    {F : Interval (Mat 𝕋 W.k W.k)} {g : Vec 𝕋 W.k}
    (hS : LinearSys.step_verifyKrylovSetupFloat W Δt = some (s, D, rD, nD, F, g)) : -- --- CONCL ---
    (∀ l, 0 < toReal (s l)) ∧
    ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • toRealMat W.H) - toRealMat D)‖
      ≤ toReal rD ∧
    ‖Real.MatExp.scaleConj (toRealVec s) (toRealMat D)‖ ≤ toReal nD ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ toReal Δt → exp (t • toRealMat W.H) - 1 -
      (t / toReal Δt) • (exp (toReal Δt • toRealMat W.H) - 1) ∈ F.toSet) ∧
    (∀ l, g l = LinearSys.step_verifyKrylovMagFloat ⟨F.inf l, F.sup l⟩ s) := by -- --- PROOF ---
  have key : ∀ (hpos : (List.finRange W.k).all
      (fun l => ltStrict FloatOps.zero (MatExp.balanceScalesFloat W.H l)) = true)
      (D' : Mat 𝕋 W.k W.k) (rD' : 𝕋) (η : ℕ) (F' : Interval (Mat 𝕋 W.k W.k)),
      MatExp.expBallFloat W.H (MatExp.balanceScalesFloat W.H) Δt = some (D', rD') →
      MatExp.verifyCorrectionStateFloat W.H (MatExp.balanceScalesFloat W.H) Δt = some (η, F') →
      LinearSys.step_verifyKrylovSetupFloat W Δt = some (MatExp.balanceScalesFloat W.H, D', rD',
        maximum FloatOps.zero (maximumOver fun l => sumUp fun j =>
          divUp (mulUp (absolute (D' l j)) (MatExp.balanceScalesFloat W.H j))
            (MatExp.balanceScalesFloat W.H l)), F',
        (Interval.point fun l => sumUp fun j =>
          mulUp (maximum (absolute (F'.inf l j)) (absolute (F'.sup l j)))
            (MatExp.balanceScalesFloat W.H j)).materialise.sup) := by
    intro hpos D' rD' η F' hb hc
    unfold LinearSys.step_verifyKrylovSetupFloat
    rw [if_neg (by rw [hpos]; decide), hb, hc]
  -- every other case is `none`
  cases hpos : (List.finRange W.k).all
      (fun l => ltStrict FloatOps.zero (MatExp.balanceScalesFloat W.H l)) with
  | false =>
    exfalso
    unfold LinearSys.step_verifyKrylovSetupFloat at hS
    dsimp only at hS
    rw [if_pos (by rw [hpos]; decide)] at hS
    cases hS
  | true =>
-- the scales are positive; the two matches must succeed
  have hs : ∀ l, 0 < toReal (MatExp.balanceScalesFloat W.H l) := fun l => by
    have := toReal_lt_of_ltStrict (List.all_eq_true.mp hpos l (List.mem_finRange l))
    rwa [toReal_zero] at this
  have hnone : ∀ (o₁ : Option (Mat 𝕋 W.k W.k × 𝕋)) (o₂ : Option (ℕ × Interval (Mat 𝕋 W.k W.k))),
      MatExp.expBallFloat W.H (MatExp.balanceScalesFloat W.H) Δt = o₁ →
      MatExp.verifyCorrectionStateFloat W.H (MatExp.balanceScalesFloat W.H) Δt = o₂ →
      (o₁ = none ∨ o₂ = none) → False := by
    intro o₁ o₂ h₁ h₂ h
    unfold LinearSys.step_verifyKrylovSetupFloat at hS
    dsimp only at hS
    rw [if_neg (by rw [hpos]; decide), h₁, h₂] at hS
    rcases h with rfl | rfl
    · cases hS
    · rcases o₁ with _ | ⟨_, _⟩ <;> cases hS
  -- the ball and the correction matrix, then the setup's values
  rcases hb : MatExp.expBallFloat W.H (MatExp.balanceScalesFloat W.H) Δt with _ | ⟨D', rD'⟩
  · exact (hnone _ _ hb rfl (Or.inl rfl)).elim
  rcases hc : MatExp.verifyCorrectionStateFloat W.H (MatExp.balanceScalesFloat W.H) Δt
    with _ | ⟨η, F'⟩
  · exact (hnone _ _ hb hc (Or.inr rfl)).elim
  rw [key hpos D' rD' η F' hb hc] at hS
  simp only [Option.some.injEq, Prod.mk.injEq] at hS
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hS
  refine ⟨hs, MatExp.norm_scaleConj_exp_sub_le_expBallFloat W.H hs hΔt.le (D', rD')
      (Option.mem_def.mpr hb),
    LinearSys.aux_norm_le_nD hs D', fun t ht0 htr =>
      MatExp.expDiff_mem_verifyCorrectionStateFloat W.H hs hΔt (η, F') (Option.mem_def.mpr hc) t
        ht0 htr, fun l => ?_⟩
  simp only [Interval.materialise_eq, Interval.point, LinearSys.step_verifyKrylovMagFloat]

/-- The iterate's error after a step: `e^{HΔt}` carries `E` by `‖D̃‖ + r`, the ball adds
`r ‖ŷ‖`, the rounding of `D̃ ŷ` its gap. -/
private theorem LinearSys.aux_error_step {k : ℕ} {s : Vec 𝕋 k} (hs : ∀ l, 0 < toReal (s l))
    {D : Mat 𝕋 k k} {rD nD E : 𝕋} {M : Mat ℝ k k}
    (hrD : ‖Real.MatExp.scaleConj (toRealVec s) (M - toRealMat D)‖ ≤ toReal rD)
    (hnD : ‖Real.MatExp.scaleConj (toRealVec s) (toRealMat D)‖ ≤ toReal nD)
    (hE : 0 ≤ toReal E) {ψ : Vec ℝ k} {y : Vec 𝕋 k}
    (hψ : ∀ l, |ψ l - toReal (y l)| ≤ toReal (s l) * toReal E) : -- --- CONCL ---
    let Dy : Interval (Vec 𝕋 k) := (⟨mulVecDown D y, mulVecUp D y⟩ : Interval _).materialise
    let ym := maximumOver fun l => divUp (absolute (y l)) (s l)
    let gap := maximumOver fun l => divUp (subUp (Dy.sup l) (Dy.inf l)) (s l)
    let E' := maximum E (addUp (addUp (mulUp (addUp nD rD) E) (mulUp rD ym)) gap)
    toReal E ≤ toReal E' ∧
      ∀ l, |(M *ᵥ ψ) l - toReal (Dy.sup l)| ≤ toReal (s l) * toReal E' := by -- --- PROOF ---
  intro Dy ym gap E'
  have hs' : ∀ l, 0 < toRealVec s l := hs
  have hrD0 : 0 ≤ toReal rD := le_trans (norm_nonneg _) hrD
  have hnD0 : 0 ≤ toReal nD := le_trans (norm_nonneg _) hnD
  have hE'1 : toReal E ≤ toReal E' := by
    simp only [E', toReal_maximum]; exact le_max_left _ _
  refine ⟨hE'1, fun l => ?_⟩
  -- the three parts of `ψ' - ŷ'`
  have hM : ‖Real.MatExp.scaleConj (toRealVec s) M‖ ≤ toReal nD + toReal rD := by
    have h := LinearSys.aux_scaleConj_add (toRealVec s) (toRealMat D) (M - toRealMat D)
    rw [add_sub_cancel] at h
    rw [h]; exact le_trans (norm_add_le _ _) (by linarith)
  have hym : 0 ≤ toReal ym :=
    le_trans (div_nonneg (abs_nonneg (toReal (y l))) (hs l).le) (le_trans
      (by rw [← toReal_absolute]; exact div_le_divUp _ _ (hs l))
      (le_maximumOver (fun l => divUp (absolute (y l)) (s l)) l))
  have hyb : ∀ j, |toRealVec y j| ≤ toRealVec s j * toReal ym := fun j => by
    have h1 := le_trans (div_le_divUp (absolute (y j)) (s j) (hs j))
      (le_maximumOver (fun l => divUp (absolute (y l)) (s l)) j)
    rw [toReal_absolute, div_le_iff₀ (hs j)] at h1
    simp only [toRealVec]; linarith
  have e1 := LinearSys.aux_scaled_mulVec hs' M hM hE (x := ψ - toRealVec y) (fun j => hψ j) l
  have e2 := LinearSys.aux_scaled_mulVec hs' (M - toRealMat D) hrD hym hyb l
  -- the rounding of `D̃ ŷ`
  have hdn : toReal (Dy.inf l) ≤ (toRealMat D *ᵥ toRealVec y) l := by
    simp only [Dy, Interval.materialise_eq, mulVecDown]; exact dotDown_le _ _
  have hup : (toRealMat D *ᵥ toRealVec y) l ≤ toReal (Dy.sup l) := by
    simp only [Dy, Interval.materialise_eq, mulVecUp]; exact le_dotUp _ _
  have hgap : toReal (Dy.sup l) - toReal (Dy.inf l) ≤ toReal (s l) * toReal gap := by
    have h1 := le_trans (div_le_divUp (subUp (Dy.sup l) (Dy.inf l)) (s l) (hs l))
      (le_maximumOver (fun l => divUp (subUp (Dy.sup l) (Dy.inf l)) (s l)) l)
    rw [div_le_iff₀ (hs l)] at h1
    linarith [sub_le_subUp (Dy.sup l) (Dy.inf l)]
  have hsplit : (M *ᵥ ψ) l - toReal (Dy.sup l) = (M *ᵥ (ψ - toRealVec y)) l
      + ((M - toRealMat D) *ᵥ toRealVec y) l + ((toRealMat D *ᵥ toRealVec y) l -
        toReal (Dy.sup l)) := by
    rw [mulVec_sub, sub_mulVec]; simp only [Pi.sub_apply]; ring
  rw [hsplit]
  -- `s ((‖D̃‖ + r) E + r ‖ŷ‖ + gap) ≤ s E'`
  have hgap0 : 0 ≤ toReal (Dy.sup l) - toReal (Dy.inf l) := by linarith
  have hsum : toReal (s l) * ((toReal nD + toReal rD) * toReal E) + toReal (s l) *
      (toReal rD * toReal ym) + toReal (s l) * toReal gap ≤ toReal (s l) * toReal E' := by
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hs l).le
    simp only [E', toReal_maximum]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (add_le_addUp _ _)
    refine add_le_add (le_trans ?_ (add_le_addUp _ _)) le_rfl
    refine add_le_add (le_trans ?_ (mul_le_mulUp _ _)) (mul_le_mulUp _ _)
    exact mul_le_mul_of_nonneg_right (add_le_addUp _ _) hE
-- the triangle inequality over the three parts
  simp only [toRealVec] at e1 e2
  calc |(M *ᵥ (ψ - toRealVec y)) l + ((M - toRealMat D) *ᵥ toRealVec y) l +
        ((toRealMat D *ᵥ toRealVec y) l - toReal (Dy.sup l))|
      ≤ |(M *ᵥ (ψ - toRealVec y)) l| + |((M - toRealMat D) *ᵥ toRealVec y) l| +
        |(toRealMat D *ᵥ toRealVec y) l - toReal (Dy.sup l)| := abs_add_three _ _ _
    _ ≤ _ := by
        have h3 : |(toRealMat D *ᵥ toRealVec y) l - toReal (Dy.sup l)| ≤ toReal (s l) *
            toReal gap := by
          rw [abs_le]; constructor <;> linarith
        linarith

/-- `e^{(a+b)M} = e^{aM} e^{bM}`. -/
private theorem LinearSys.aux_exp_add {k : ℕ} (M : Mat ℝ k k) (a b : ℝ) :
    exp ((a + b) • M) = exp (a • M) * exp (b • M) := by
  have hc : Commute (a • M) (b • M) := ((Commute.refl M).smul_left a).smul_right b
  rw [add_smul]
  exact exp_add_of_commute hc

/-- The row of a vector in the window holds `ν v' V`. -/
private theorem LinearSys.aux_row (W : LinearSys.VerifyKrylovWindow 𝕋 n)
    (v : Vec 𝕋 n) : -- --- CONCL ---
    ∀ l, toReal ((LinearSys.step_verifyKrylovRowFloat W v).inf l) ≤
        (toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) l ∧
      (toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) l ≤
        toReal ((LinearSys.step_verifyKrylovRowFloat W v).sup l) := by -- --- PROOF ---
  intro l
  have hx : (toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) l
      = toReal W.ν * ∑ r, toReal (v r) * toReal (W.V r l) := by
    simp [vecMul, dotProduct, toRealVec, toRealMat]
  rw [hx]
  simp only [LinearSys.step_verifyKrylovRowFloat, Interval.materialise_eq]
  exact Interval.mul_between_corners le_rfl le_rfl (dotDown_le _ _) (le_dotUp _ _)

/-- On step `i` of a window, every vector's row value at `ψ(τ) = e^{τH} e₁` is within its term:
`ψ(τ) = (1 - θ) ψ_i + θ ψ_{i+1} + Φ ψ_i`, `Φ ∈ [F]`, the ends within `s E` and `s E'`. -/
private theorem LinearSys.aux_vec_step (W : LinearSys.VerifyKrylovWindow 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {s : Vec 𝕋 W.k} {D : Mat 𝕋 W.k W.k} {rD nD : 𝕋}
    {F : Interval (Mat 𝕋 W.k W.k)} {g : Vec 𝕋 W.k}
    (hS : LinearSys.step_verifyKrylovSetupFloat W Δt = some (s, D, rD, nD, F, g)) (i : ℕ)
    {y : Vec 𝕋 W.k} {E : 𝕋} (hE : 0 ≤ toReal E)
    (hψ : ∀ l, |(exp (((i : ℝ) * toReal Δt) • toRealMat W.H) *ᵥ
      fun l => if l.val = 0 then 1 else 0) l - toReal (y l)| ≤
        toReal (s l) * toReal E) : -- --- CONCL ---
    let Dy : Interval (Vec 𝕋 W.k) := (⟨mulVecDown D y, mulVecUp D y⟩ : Interval _).materialise
    let y' := Dy.sup
    let ym := maximumOver fun l => divUp (absolute (y l)) (s l)
    let gap := maximumOver fun l => divUp (subUp (Dy.sup l) (Dy.inf l)) (s l)
    let E' := maximum E (addUp (addUp (mulUp (addUp nD rD) E) (mulUp rD ym)) gap)
    let Fy : Interval (Vec 𝕋 W.k) :=
      (⟨fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).1,
        fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).2⟩ :
          Interval _).materialise
    0 ≤ toReal E' ∧
    (∀ l, |(exp ((((i + 1 : ℕ) : ℝ) * toReal Δt) • toRealMat W.H) *ᵥ
      fun l => if l.val = 0 then 1 else 0) l - toReal (y' l)| ≤ toReal (s l) * toReal E') ∧
    ∀ τ : ℝ, (i : ℝ) * toReal Δt ≤ τ → τ ≤ ((i : ℝ) + 1) * toReal Δt → ∀ (signed : Bool)
      (v : Vec 𝕋 n),
      (if signed then (toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) ⬝ᵥ
          (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)
        else |(toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) ⬝ᵥ
          (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)|) ≤
        toReal (LinearSys.step_verifyKrylovTermFloat signed (LinearSys.step_verifyKrylovRowFloat W
          v) s g y y' Fy E E') := by -- --- PROOF ---
  intro Dy y' ym gap E' Fy
  obtain ⟨hs, hrD, hnD, hF, hg⟩ := LinearSys.aux_setup W hΔt hS
  set H := toRealMat W.H with hH
  set e₁ : Vec ℝ W.k := fun l => if l.val = 0 then 1 else 0 with he₁
  set Δ := toReal Δt with hΔ
  set ψ₀ := exp (((i : ℝ) * Δ) • H) *ᵥ e₁ with hψ₀
  set E₁ := exp (Δ • H) with hE₁
  -- the next iterate
  have hstep := LinearSys.aux_error_step hs hrD hnD hE (ψ := ψ₀) hψ
  have hψ₁ : exp ((((i + 1 : ℕ) : ℝ) * Δ) • H) *ᵥ e₁ = E₁ *ᵥ ψ₀ := by
    rw [hψ₀, mulVec_mulVec, ← LinearSys.aux_exp_add]; push_cast; ring_nf
  have hE' : toReal E ≤ toReal E' := hstep.1
  refine ⟨le_trans hE hE', fun l => by rw [hψ₁]; exact hstep.2 l, fun τ hτ1 hτ2 signed v => ?_⟩
  -- `ψ(τ) = (1 - θ) ψ_i + θ ψ_{i+1} + Φ ŷ + Φ (ψ_i - ŷ)`
  set t' := τ - (i : ℝ) * Δ with ht'
  have ht0 : 0 ≤ t' := by linarith
  have ht1 : t' ≤ Δ := by linarith
  set θ := t' / Δ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg ht0 hΔt.le
  have hθ1 : θ ≤ 1 := (div_le_one hΔt).mpr ht1
  set Φ := exp (t' • H) - 1 - θ • (E₁ - 1) with hΦ
  have hΦF := Interval.mem_mat_iff.mp (hF t' ht0 ht1)
  have hψτ : exp (τ • H) *ᵥ e₁ = (1 - θ) • ψ₀ + θ • (E₁ *ᵥ ψ₀) +
      (Φ *ᵥ toRealVec y + Φ *ᵥ (ψ₀ - toRealVec y)) := by
    have hτ : τ = t' + (i : ℝ) * Δ := by rw [ht']; ring
    have hexp : exp (t' • H) = 1 + θ • (E₁ - 1) + Φ := by rw [hΦ]; abel
    rw [← mulVec_add, add_sub_cancel, hτ, LinearSys.aux_exp_add, ← mulVec_mulVec, ← hψ₀, hexp,
      add_mulVec, add_mulVec, smul_mulVec, sub_mulVec, sub_mulVec, one_mulVec]
    module
  rw [hψτ]
  refine LinearSys.aux_term signed _ s g y y' Fy E E' hθ0 hθ1 (fun l => (hs l).le) hE hE'
    (LinearSys.aux_row W v) hψ (fun l => hstep.2 l) (fun l => ?_) (fun l => ?_)
  · -- `Φ ŷ ∈ [F] ŷ`
    have := LinearSys.aux_dot (a := F.inf l) (b := F.sup l) (c := y) (d := y) (x := Φ l)
      (y := toRealVec y) (fun j => hΦF l j) (fun j => ⟨le_rfl, le_rfl⟩)
    simp only [Fy, Interval.materialise_eq]
    exact this
  · -- `|Φ (ψ_i - ŷ)| ≤ g E`
    rw [hg l]
    exact LinearSys.aux_mag ⟨F.inf l, F.sup l⟩ s hE (fun j => hΦF l j) fun j => hψ j

/-- `z' (c + G β)` is at most the center's term plus the generators' plus `err` times the norms. -/
private theorem LinearSys.aux_zono_bound {z : Vec ℝ n} {c : Vec 𝕋 n} {G : Mat 𝕋 n m}
    {err nR Tc : 𝕋} {Tg : Fin m → 𝕋} (herr : 0 ≤ toReal err)
    (hnR : ‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂ ≤ toReal nR)
    (hc : z ⬝ᵥ toRealVec c ≤ toReal Tc + toReal err * ‖toRealVec c‖₂)
    (hg : ∀ j, |z ⬝ᵥ fun i => toReal (G i j)| ≤
      toReal (Tg j) + toReal err * ‖fun i => toReal (G i j)‖₂)
    {β : Fin m → ℝ} (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    z ⬝ᵥ (toRealVec c + toRealMat G *ᵥ β) ≤
      toReal (addUp (mulUp err nR) (addUp Tc (sumUp Tg))) := by -- --- PROOF ---
  have hsplit : z ⬝ᵥ (toRealVec c + toRealMat G *ᵥ β) = z ⬝ᵥ toRealVec c +
      ∑ j, β j * (z ⬝ᵥ fun i => toReal (G i j)) := by
    rw [dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec, toRealMat, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hgen : ∀ j, β j * (z ⬝ᵥ fun i => toReal (G i j)) ≤
      toReal (Tg j) + toReal err * ‖fun i => toReal (G i j)‖₂ := fun j =>
    le_trans (le_abs_self _) (by
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (hβ j)) (hg j))
-- sum the generators' bounds, then round
  rw [hsplit]
  have h1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hgen j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 : toReal err * (‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂) ≤
      toReal (mulUp err nR) :=
    le_trans (mul_le_mul_of_nonneg_left hnR herr) (mul_le_mulUp _ _)
  have h3 := sum_le_sumUp Tg
  have h4 := add_le_addUp Tc (sumUp Tg)
  have h5 := add_le_addUp (mulUp err nR) (addUp Tc (sumUp Tg))
  nlinarith

/-- The rounded sum of the norms bounds the norms. -/
private theorem LinearSys.aux_norms (c : Vec 𝕋 n) (G : Mat 𝕋 n m) :
    ‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂ ≤
      toReal (addUp (normUp 30 c) (sumUp fun j => normUp 30 fun i => G i j)) := by
  exact le_trans (add_le_add (norm₂_le_normUp 30 fun j => le_rfl)
    (le_trans (Finset.sum_le_sum fun j _ => norm₂_le_normUp 30 fun i => le_rfl) (sum_le_sumUp _)))
    (add_le_addUp _ _)

/-- `z = ν V ψ + e` gives `z' v = (ν v' V) ψ + e' v`. -/
private theorem LinearSys.aux_zdot {k : ℕ} {z e : Vec ℝ n} {ν : ℝ} {V : Mat ℝ n k} {ψ : Vec ℝ k}
    (hz : z = ν • (V *ᵥ ψ) + e) (v : Vec ℝ n) :
    z ⬝ᵥ v = (ν • (v ᵥ* V)) ⬝ᵥ ψ + e ⬝ᵥ v := by
  rw [hz, add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm (V *ᵥ ψ),
    dotProduct_mulVec]

/-- The input set `u_c + G_U [-1, 1]^p`. -/
private def LinearSys.aux_U (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) : Set (Vec ℝ n) :=
  (fun γ => toRealVec uc + toRealMat GU *ᵥ γ) '' Set.Icc (-1) 1

/-- The bound `b` holds `w' x(t)` over step `j`. -/
private def LinearSys.aux_claim (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) (wr : Vec ℝ n) (Δ : ℝ) (j : ℕ) (b : 𝕋) : Prop :=
  ∀ t : ℝ, (j : ℝ) * Δ ≤ t → t ≤ ((j : ℝ) + 1) * Δ → ∀ β : Fin m → ℝ, (∀ q, |β q| ≤ 1) →
    ∀ y ∈ sys.inputReach (S := ExactSet) (LinearSys.aux_U uc GU) t,
      wr ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ β) + y) ≤ toReal b

/-- The integral `I` bounds the integrands of the `j` steps so far. -/
private def LinearSys.aux_intInv (sys : LinearSys 𝕋 n) (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p)
    (wr : Vec ℝ n) (Δ : ℝ) (j : ℕ) (I : 𝕋) : Prop :=
  ∃ J : ℕ → ℝ, (∀ i < j, ∀ σ : ℝ, (i : ℝ) * Δ ≤ σ → σ ≤ ((i : ℝ) + 1) * Δ →
    ∀ u ∈ LinearSys.aux_U uc GU, wr ⬝ᵥ (exp (σ • toRealMat sys.A) *ᵥ u) ≤ J i) ∧
    ∑ i ∈ Finset.range j, Δ * J i ≤ toReal I

/-- The bounds so far, latest first, hold their `j` steps. -/
private def LinearSys.aux_outInv (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) (wr : Vec ℝ n) (Δ : ℝ) (j : ℕ) (out : List 𝕋) : Prop :=
  out.length = j ∧ ∀ i (hi : i < out.reverse.length),
    LinearSys.aux_claim sys c G uc GU wr Δ i out.reverse[i]

/-- The input set is bounded. -/
private theorem LinearSys.aux_U_bdd (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) :
    Bornology.IsBounded (LinearSys.aux_U uc GU) := by
  refine (isCompact_Icc.image ?_).isBounded
  fun_prop

/-- One step `O + i` of a window whose terms `T` bound its rows' values: the integrand bounds the
input's over the step, the bound holds the step, and both invariants move on by one. -/
private theorem LinearSys.aux_step_facts (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) (W : LinearSys.VerifyKrylovWindow 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {nR nU : 𝕋}
    (hnR : ‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂ ≤ toReal nR)
    (hnU : ‖toRealVec uc‖₂ + ∑ j, ‖fun i => toReal (GU i j)‖₂ ≤ toReal nU) (wr : Vec ℝ n)
    (O K i : ℕ) (hiK : i + 1 ≤ K) (herr : 0 ≤ toReal W.err)
    (hwin : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (K : ℝ) * toReal Δt → ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal W.err ∧
      wr ᵥ* exp (((O : ℝ) * toReal Δt + τ) • toRealMat sys.A) = toReal W.ν • (toRealMat W.V *ᵥ
        (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)) + e)
    (T : Bool → Vec 𝕋 n → 𝕋)
    (hτ : ∀ τ : ℝ, (i : ℝ) * toReal Δt ≤ τ → τ ≤ ((i : ℝ) + 1) * toReal Δt → ∀ (signed : Bool)
      (v : Vec 𝕋 n),
      (if signed then (toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) ⬝ᵥ
          (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)
        else |(toReal W.ν • (toRealVec v ᵥ* toRealMat W.V)) ⬝ᵥ
          (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)|) ≤ toReal (T signed v))
    {I : 𝕋} {out : List 𝕋} (hI : LinearSys.aux_intInv sys uc GU wr (toReal Δt) (O + i) I)
    (hO : LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) (O + i) out) : -- --- CONCL ---
    LinearSys.aux_intInv sys uc GU wr (toReal Δt) (O + i + 1) (addUp I (mulUp Δt
      (addUp (mulUp W.err nU) (addUp (T true uc) (sumUp fun j => T false fun i => GU i j))))) ∧
    LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) (O + i + 1)
      (addUp (addUp (addUp (mulUp W.err nR) (addUp (T true c) (sumUp fun j => T false fun i =>
        G i j))) I) (mulUp Δt (maximum (addUp (mulUp W.err nU) (addUp (T true uc)
          (sumUp fun j => T false fun i => GU i j))) FloatOps.zero)) :: out) := by -- --- PROOF ---
  set Δ := toReal Δt with hΔ
  set hom := addUp (mulUp W.err nR) (addUp (T true c) (sumUp fun j => T false fun i => G i j))
  set integ := addUp (mulUp W.err nU) (addUp (T true uc) (sumUp fun j => T false fun i => GU i j))
  set j := O + i with hj
  -- at a time of the step, `z = w' e^{σA}` is within every vector's term plus `err ‖v‖₂`
  have hz : ∀ σ : ℝ, (j : ℝ) * Δ ≤ σ → σ ≤ ((j : ℝ) + 1) * Δ → ∀ x : Vec 𝕋 n,
      (wr ᵥ* exp (σ • toRealMat sys.A)) ⬝ᵥ toRealVec x ≤ toReal (T true x) +
        toReal W.err * ‖toRealVec x‖₂ ∧
      |(wr ᵥ* exp (σ • toRealMat sys.A)) ⬝ᵥ toRealVec x| ≤ toReal (T false x) +
        toReal W.err * ‖toRealVec x‖₂ := by
    intro σ h1 h2 x
    have hjc : (j : ℝ) = O + i := by rw [hj]; push_cast; ring
    obtain ⟨e, he, heq⟩ := hwin (σ - O * Δ) (by nlinarith [hΔt, (Nat.cast_nonneg i : (0:ℝ) ≤ i)])
      (le_trans (by nlinarith) (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hiK : ((i : ℝ) + 1) ≤ K) hΔt.le))
    rw [show (O : ℝ) * Δ + (σ - O * Δ) = σ by ring] at heq
    have hd := LinearSys.aux_zdot heq (toRealVec x)
-- the window's local time `τ = σ - O Δ` lies in step `i`
    have hτ1 : (i : ℝ) * Δ ≤ σ - O * Δ := by nlinarith
    have hτ2 : σ - O * Δ ≤ ((i : ℝ) + 1) * Δ := by nlinarith
    have he' : |e ⬝ᵥ toRealVec x| ≤ toReal W.err * ‖toRealVec x‖₂ :=
      le_trans (abs_dotProduct_le_norm₂_mul_norm₂ _ _)
        (mul_le_mul_of_nonneg_right he (norm₂_nonneg _))
    have ht := hτ _ hτ1 hτ2 true x
    have hf := hτ _ hτ1 hτ2 false x
    simp only [if_true, Bool.false_eq_true, if_false] at ht hf
    rw [hd]
    exact ⟨by linarith [le_abs_self (e ⬝ᵥ toRealVec x)],
      le_trans (abs_add_le _ _) (by linarith)⟩
  -- the integrand over the step
  have hJ : ∀ σ : ℝ, (j : ℝ) * Δ ≤ σ → σ ≤ ((j : ℝ) + 1) * Δ →
      ∀ u ∈ LinearSys.aux_U uc GU, wr ⬝ᵥ (exp (σ • toRealMat sys.A) *ᵥ u) ≤ toReal integ := by
    rintro σ h1 h2 u ⟨γ, hγ, rfl⟩
    rw [dotProduct_mulVec]
    exact LinearSys.aux_zono_bound herr hnU (hz σ h1 h2 uc).1
      (fun q => (hz σ h1 h2 fun i => GU i q).2)
      fun q => abs_le.mpr ⟨(hγ.1 q), (hγ.2 q)⟩
  obtain ⟨J, hJs, hsum⟩ := hI
  set J' : ℕ → ℝ := fun q => if q < j then J q else toReal integ with hJ'
  have hJ's : ∀ q ≤ j, ∀ σ : ℝ, (q : ℝ) * Δ ≤ σ → σ ≤ ((q : ℝ) + 1) * Δ →
      ∀ u ∈ LinearSys.aux_U uc GU, wr ⬝ᵥ (exp (σ • toRealMat sys.A) *ᵥ u) ≤ J' q := by
    intro q hq σ h1 h2 u hu
    rcases lt_or_eq_of_le hq with hlt | rfl
    · simp only [hJ', if_pos hlt]; exact hJs q hlt σ h1 h2 u hu
    · simp only [hJ', lt_irrefl, if_false]; exact hJ σ h1 h2 u hu
  have hsumJ' : ∑ q ∈ Finset.range j, Δ * J' q = ∑ q ∈ Finset.range j, Δ * J q :=
    Finset.sum_congr rfl fun q hq => by
      simp only [hJ', if_pos (Finset.mem_range.mp hq)]
  have hJ'j : J' j = toReal integ := by simp [hJ']
  refine ⟨⟨J', fun q hq => hJ's q (Nat.lt_succ_iff.mp hq), ?_⟩, ⟨by simp [hO.1], ?_⟩⟩
  · -- the integral moves on by `Δ integrand`
    rw [Finset.sum_range_succ, hsumJ', hJ'j]
    exact le_trans (add_le_add hsum (mul_le_mulUp _ _)) (add_le_addUp _ _)
  · -- the new bound holds step `j`, the old ones theirs
    intro q hq
    have hlen : out.length = j := hO.1
    have hq' : q < j + 1 := by simpa [hlen] using hq
    simp only [List.reverse_cons, List.getElem_append, List.length_reverse]
    split_ifs with hlt
    · exact hO.2 q (by rw [List.length_reverse]; exact hlt)
-- the new bound: the state's part by the terms, the input's by the integrands
    · have heq : q = j := by omega
      subst heq
      simp only [List.getElem_singleton]
      intro t h1 h2 β hβ y hy
      rw [dotProduct_add, dotProduct_mulVec]
      have h1' : (j : ℝ) * Δ ≤ t := h1
      have h2' : t ≤ ((j : ℝ) + 1) * Δ := h2
      have hh := LinearSys.aux_zono_bound herr hnR (hz t h1' h2' c).1
        (fun q => (hz t h1' h2' fun i => G i q).2) hβ
      have hin := LinearSys.dotProduct_le_of_mem_inputReach sys (LinearSys.aux_U_bdd uc GU) wr
        hΔt.le (j := j) h1' h2' J' hJ's y hy
      rw [hsumJ', hJ'j] at hin
      have hmax : Δ * max (toReal integ) 0 ≤ toReal (mulUp Δt (maximum integ FloatOps.zero)) := by
        have h := mul_le_mulUp Δt (maximum integ FloatOps.zero)
        rw [toReal_maximum, toReal_zero] at h
        exact h
      have h3 := add_le_addUp hom I
      have h4 := add_le_addUp (addUp hom I) (mulUp Δt (maximum integ FloatOps.zero))
      linarith

/-- `L` steps of a window from local step `i` keep the integral's and the bounds' invariants. -/
private theorem LinearSys.aux_steps (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) (W : LinearSys.VerifyKrylovWindow 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {s : Vec 𝕋 W.k} {D : Mat 𝕋 W.k W.k} {rD nD : 𝕋}
    {F : Interval (Mat 𝕋 W.k W.k)} {g : Vec 𝕋 W.k}
    (hS : LinearSys.step_verifyKrylovSetupFloat W Δt = some (s, D, rD, nD, F, g)) {nR nU : 𝕋}
    (hnR : ‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂ ≤ toReal nR)
    (hnU : ‖toRealVec uc‖₂ + ∑ j, ‖fun i => toReal (GU i j)‖₂ ≤ toReal nU) (wr : Vec ℝ n)
    (O K : ℕ)
    (hwin : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (K : ℝ) * toReal Δt → ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal W.err ∧
      wr ᵥ* exp (((O : ℝ) * toReal Δt + τ) • toRealMat sys.A) = toReal W.ν • (toRealMat W.V *ᵥ
        (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)) + e) : -- --- CONCL ---
    ∀ (L i : ℕ) (y : Vec 𝕋 W.k) (E I : 𝕋) (out : List 𝕋), i + L ≤ K → 0 ≤ toReal E →
      (∀ l, |(exp (((i : ℝ) * toReal Δt) • toRealMat W.H) *ᵥ
        fun l => if l.val = 0 then 1 else 0) l - toReal (y l)| ≤ toReal (s l) * toReal E) →
      LinearSys.aux_intInv sys uc GU wr (toReal Δt) (O + i) I →
      LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) (O + i) out →
      LinearSys.aux_intInv sys uc GU wr (toReal Δt) (O + i + L)
          (LinearSys.step_verifyKrylovStepsFloat c G uc GU W s D rD nD F g nR nU Δt L y E I
            out).1 ∧
      LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) (O + i + L)
          (LinearSys.step_verifyKrylovStepsFloat c G uc GU W s D rD nD F g nR nU Δt L y E I
            out).2 := by -- --- PROOF ---
  have herr : 0 ≤ toReal W.err := by
    obtain ⟨e, he, -⟩ := hwin 0 le_rfl (mul_nonneg (Nat.cast_nonneg _) hΔt.le)
    exact le_trans (norm₂_nonneg _) he
  intro L
  induction L with
  | zero =>
    intro i y E I out _ _ _ hI hO
    exact ⟨hI, hO⟩
  | succ L ih =>
-- one step: the next iterate and the terms, then the rest of the window
  intro i y E I out hiL hE hψ hI hO
  have hv := LinearSys.aux_vec_step W hΔt hS i hE hψ
  dsimp only at hv
  obtain ⟨hE'0, hψ', hτ⟩ := hv
  have key := LinearSys.aux_step_facts sys c G uc GU W hΔt hnR hnU wr O K i (by omega) herr hwin
    (fun signed v => LinearSys.step_verifyKrylovTermFloat signed
      (LinearSys.step_verifyKrylovRowFloat W v) s g y
      ((⟨mulVecDown D y, mulVecUp D y⟩ : Interval (Vec 𝕋 W.k)).materialise.sup)
      ((⟨fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).1,
        fun l => (LinearSys.step_verifyKrylovDotFloat (F.inf l) (F.sup l) y y).2⟩ :
          Interval (Vec 𝕋 W.k)).materialise) E
      (maximum E (addUp (addUp (mulUp (addUp nD rD) E)
        (mulUp rD (maximumOver fun l => divUp (absolute (y l)) (s l))))
        (maximumOver fun l => divUp (subUp
          ((⟨mulVecDown D y, mulVecUp D y⟩ : Interval (Vec 𝕋 W.k)).materialise.sup l)
          ((⟨mulVecDown D y, mulVecUp D y⟩ : Interval (Vec 𝕋 W.k)).materialise.inf l)) (s l)))))
    hτ hI hO
  rw [show O + i + (L + 1) = O + (i + 1) + L by omega, LinearSys.step_verifyKrylovStepsFloat]
  exact ih (i + 1) _ _ _ _ (by omega) hE'0 hψ' key.1 key.2

/-- The windows in order, from `o` window steps done, keep the invariants and end in `o ratio + rem`
bounds that hold their steps. -/
private theorem LinearSys.aux_windows (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (uc : Vec 𝕋 n) (GU : Mat 𝕋 n p) {Δt : 𝕋} (hΔt : 0 < toReal Δt) {nR nU : 𝕋}
    (hnR : ‖toRealVec c‖₂ + ∑ j, ‖fun i => toReal (G i j)‖₂ ≤ toReal nR)
    (hnU : ‖toRealVec uc‖₂ + ∑ j, ‖fun i => toReal (GU i j)‖₂ ≤ toReal nU) (wr : Vec ℝ n)
    (ratio : ℕ) : -- --- CONCL ---
    ∀ (ws : List (LinearSys.VerifyKrylovWindow 𝕋 n)) (o rem : ℕ) (I : 𝕋) (out : List 𝕋),
      (∀ q (hq : q < ws.length) (τ : ℝ), 0 ≤ τ → τ ≤ ((ws[q].steps * ratio : ℕ) : ℝ) * toReal Δt →
        ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal ws[q].err ∧
          wr ᵥ* exp (((((o + ((ws.take q).map (·.steps)).sum) * ratio : ℕ) : ℝ) * toReal Δt + τ) •
            toRealMat sys.A) = toReal ws[q].ν • (toRealMat ws[q].V *ᵥ
              (exp (τ • toRealMat ws[q].H) *ᵥ fun l => if l.val = 0 then 1 else 0)) + e) →
      LinearSys.aux_intInv sys uc GU wr (toReal Δt) (o * ratio) I →
      LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) (o * ratio) out →
      ∀ B, LinearSys.step_verifyKrylovWindowsFloat c G uc GU nR nU Δt ratio ws rem I out = some B →
        B.length = o * ratio + rem ∧ ∀ j (hj : j < B.length),
          LinearSys.aux_claim sys c G uc GU wr (toReal Δt) j B[j] := by -- --- PROOF ---
  -- no steps left: the bounds so far, in order
  have hdone : ∀ (ws : List (LinearSys.VerifyKrylovWindow 𝕋 n)) (d : ℕ) (I : 𝕋) (out : List 𝕋),
      LinearSys.aux_outInv sys c G uc GU wr (toReal Δt) d out →
      ∀ B, LinearSys.step_verifyKrylovWindowsFloat c G uc GU nR nU Δt ratio ws 0 I out = some B →
        B.length = d ∧ ∀ j (hj : j < B.length),
          LinearSys.aux_claim sys c G uc GU wr (toReal Δt) j B[j] := by
    intro ws d I out hO B hB
    have hB' : B = out.reverse := by
      cases ws <;> simp only [LinearSys.step_verifyKrylovWindowsFloat, Option.some.injEq] at hB <;>
        exact hB.symm
    subst hB'
    exact ⟨by rw [List.length_reverse]; exact hO.1, hO.2⟩
-- window by window
  intro ws
  induction ws with
  | nil =>
    intro o rem I out _ _ hO B hB
    cases rem with
    | zero => simpa using hdone [] _ I out hO B hB
    | succ rem => simp [LinearSys.step_verifyKrylovWindowsFloat] at hB
  | cons W ws ih =>
  intro o rem I out hw hI hO B hB
  cases rem with
  | zero => simpa using hdone _ _ I out hO B hB
  | succ rem =>
  rw [LinearSys.step_verifyKrylovWindowsFloat] at hB
  rcases hS : LinearSys.step_verifyKrylovSetupFloat W Δt with _ | ⟨s, D, rD, nD, F, g⟩
  · rw [hS] at hB; cases hB
  rw [hS] at hB
  dsimp only at hB
  set K := W.steps * ratio with hK
  set O := o * ratio with hO'
  -- the first window, from `e₁` with no error
  have hw0 : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (K : ℝ) * toReal Δt → ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal W.err ∧
      wr ᵥ* exp (((O : ℝ) * toReal Δt + τ) • toRealMat sys.A) = toReal W.ν • (toRealMat W.V *ᵥ
        (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0)) + e := by
    intro τ h0 h1
    obtain ⟨e, he, heq⟩ := hw 0 (by simp) τ h0 h1
    exact ⟨e, he, heq⟩
  have hψ0 : ∀ l, |(exp ((((0 : ℕ) : ℝ) * toReal Δt) • toRealMat W.H) *ᵥ
      fun l => if l.val = 0 then 1 else 0) l -
      toReal ((fun l : Fin W.k => if l.val = 0 then (FloatOps.one : 𝕋) else FloatOps.zero) l)| ≤
        toReal (s l) * toReal (FloatOps.zero : 𝕋) := fun l => by
    simp only [Nat.cast_zero, zero_mul, zero_smul, exp_zero, one_mulVec, toReal_zero, mul_zero]
    split_ifs <;> simp [SoundFloatArithmetic.toReal_one, SoundFloatArithmetic.toReal_zero]
  have hst := LinearSys.aux_steps sys c G uc GU W hΔt hS hnR hnU wr O K hw0 (min K (rem + 1)) 0
    _ FloatOps.zero I out (by omega) (by rw [toReal_zero]) hψ0 (by simpa using hI)
    (by simpa using hO)
  simp only [Nat.add_zero] at hst
  by_cases hL : K ≤ rem + 1
  · -- the whole window: the next ones from `o + steps`
    rw [min_eq_left hL] at hst hB
    have hOK : (o + W.steps) * ratio = O + K := by rw [hO', hK]; ring
    have := ih (o + W.steps) (rem + 1 - K) _ _ (fun q hq τ h0 h1 => by
        obtain ⟨e, he, heq⟩ := hw (q + 1) (by simp; omega) τ h0 h1
        have hsum : o + (((W :: ws).take (q + 1)).map (·.steps)).sum =
            o + W.steps + ((ws.take q).map (·.steps)).sum := by simp [Nat.add_assoc]
        rw [hsum] at heq
        exact ⟨e, he, heq⟩)
      (by rw [hOK]; exact hst.1) (by rw [hOK]; exact hst.2) B hB
    rw [hOK] at this
    exact ⟨by rw [this.1]; omega, this.2⟩
  · -- the steps left end in this window
    rw [min_eq_right (by omega)] at hst hB
    rw [Nat.sub_self] at hB
    have := hdone ws _ _ _ hst.2 B hB
    exact ⟨this.1, this.2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyKrylovBoundsFloat_sound (sys : LinearSys 𝕋 n) {c : Vec 𝕋 n}
    {G : Mat 𝕋 n m} {uc : Vec 𝕋 n} {GU : Mat 𝕋 n p} {w : Vec 𝕋 n}
    {wins : List (LinearSys.VerifyKrylovWindow 𝕋 n)}
    {ratio : ℕ} {Δt : 𝕋} {N : ℕ}
    (hwin : LinearSys.IsVerifyKrylovWindows (toRealMat sys.A) (toRealVec w)
      ((ratio : ℝ) * toReal Δt) wins) : -- --- CONCL ---
    ∀ B ∈ LinearSys.verifyKrylovBoundsFloat c G uc GU w wins ratio Δt N, B.length = N ∧
      ∀ j (hj : j < B.length) (t : ℝ), (j : ℝ) * toReal Δt ≤ t →
        t ≤ ((j : ℝ) + 1) * toReal Δt → ∀ β : Fin m → ℝ, (∀ q, |β q| ≤ 1) →
        ∀ y ∈ sys.inputReach (S := ExactSet)
          ((fun γ => toRealVec uc + toRealMat GU *ᵥ γ) '' Set.Icc (-1) 1) t,
          toRealVec w ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ β) + y)
            ≤ toReal B[j] := by -- --- PROOF ---
  intro B hB
  rw [Option.mem_def] at hB
  unfold LinearSys.verifyKrylovBoundsFloat at hB
  split_ifs at hB with h1 h2
  · -- a zero direction: every bound `0` holds
    cases hB
    have hw0 : toRealVec w = 0 := funext fun i => by
      have h := List.all_eq_true.mp h2 i (List.mem_finRange i)
      rw [Bool.and_eq_true] at h
      have ha := toReal_le_of_le h.1
      have hb := toReal_le_of_le h.2
      rw [toReal_zero] at ha hb
      exact le_antisymm ha hb
    refine ⟨List.length_replicate, fun j hj t _ _ β _ y _ => ?_⟩
    rw [hw0, zero_dotProduct, List.getElem_replicate, toReal_zero]
  · -- the windows from `t = 0`
    have hΔt : 0 < toReal Δt := by
      have h : ltStrict FloatOps.zero Δt = true := by
        revert h1; cases ltStrict FloatOps.zero Δt <;> simp
      simpa [toReal_zero] using toReal_lt_of_ltStrict h
    have h := LinearSys.aux_windows sys c G uc GU hΔt (LinearSys.aux_norms c G)
      (LinearSys.aux_norms uc GU) (toRealVec w) ratio wins 0 N FloatOps.zero []
      (fun q hq τ h0 h1 => by
        obtain ⟨e, he, heq⟩ := hwin q hq τ h0 (by push_cast at h1; linarith)
        refine ⟨e, he, ?_⟩
        rw [← heq]
        congr 3
        push_cast; ring)
      ⟨fun _ => 0, fun _ h => absurd h (by simp), by simp [toReal_zero]⟩
      ⟨by simp, fun _ h => absurd h (by simp)⟩ B hB
    exact ⟨by simpa using h.1, fun j hj => h.2 j hj⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
