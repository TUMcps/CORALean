module

public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifyKrylovWindows
public import CORALean.ContDynamics.LinearSys.Operations.VerifyKrylovWindowsFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiFloatHessenberg
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.CarryMinFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorBoundFloatOuter
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpLeWeighted
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.WindowErrorBoundFloatSound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The windows of `LinearSys.verifyKrylovWindowsFloat` hold `w' e^{tA}`

With `v_i = e^{T_i A'} w` the true state at the start `T_i` of window `i` and `x_i` its float
start, `‖v_i - x_i‖₂ ≤ C_i`. In the window, `e^{τA'} v_i - ν V e^{τH} e₁` is
`e^{τA'}(v_i - x_i)`, at most `e^{τ μ_A} C_i ≤ g C_i` (`Krylov.norm_exp_le_weighted` with the
identity weight, `μ_A` from `Krylov.quad_le_quadBoundUp`), plus the local error
(`Krylov.error_le_errorBoundFloat`). The next start adds the ball of `e^{LH}` and the rounding of
`ν V D̃ e₁`. With a certificate, the Lyapunov carry of the transition errors bounds the same
difference (`Krylov.windowErrorBoundFloat_sound`), so the smaller one does. So every window
satisfies `LinearSys.IsVerifyKrylovWindows` on the grid `Δt₀`.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold of Arnoldi
* `A` – float system matrix
* `w` – float direction
* `Δt₀` – float step size of the windows
* `plan` – order and steps of every window
* `cert` – Lyapunov certificate `(P, L, a)` of `A'`, if any

## Hypotheses
* `hq` – at least one squaring

## Conclusion
* the windows hold `w' e^{tA}` on the grid `Δt₀`
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{τM}` grows the 2-norm by at most `e^{μτ}`, `μ` above the quadratic form of `M`. -/
private theorem LinearSys.aux_growth_norm {k : ℕ} (M : Mat ℝ k k) {μ : ℝ}
    (hμ : ∀ x : Vec ℝ k, x ⬝ᵥ (M *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (y : Vec ℝ k) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    ‖exp (τ • M) *ᵥ y‖₂ ≤ Real.exp (μ * τ) * ‖y‖₂ := by
  have h := Krylov.norm_exp_le_weighted M 1 μ 1 1 transpose_one
    (fun x => by simpa [one_mulVec] using hμ x) (fun x => by simp [one_mulVec])
    (fun x => by simp [one_mulVec]) one_pos zero_le_one y hτ
  simpa using h

/-- The first unit vector, as `Pi.single`. -/
private theorem LinearSys.aux_e₁ (k : ℕ) : -- --- CONCL ---
    (fun l : Fin (k + 1) => if l.val = 0 then (1 : ℝ) else 0) = Pi.single 0 1 := by -- --- PROOF ---
  funext l
  by_cases h : l.val = 0
  · have : l = 0 := Fin.ext h
    subst this; simp
  · have : l ≠ 0 := fun h' => h (by rw [h']; rfl)
    simp [h, this]

/-- `2^k` from doubling `1` downward is at most `2^k`. -/
private theorem LinearSys.aux_doublings (k : ℕ) : -- --- CONCL ---
    toReal ((fun y : 𝕋 => addDown y y)^[k] FloatOps.one) ≤ 2 ^ k := by -- --- PROOF ---
  induction k with
  | zero => simp [toReal_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine le_trans (addDown_le_add _ _) ?_
    rw [pow_succ]; linarith

/-- The balanced similarity with unit scales is the identity. -/
private theorem LinearSys.aux_scaleConj_one {k : ℕ} (M : Mat ℝ k k) :
    Real.MatExp.scaleConj (toRealVec (fun _ : Fin k => (FloatOps.one : 𝕋))) M = M := by
  have h1 : toRealVec (fun _ : Fin k => (FloatOps.one : 𝕋)) = fun _ => 1 := funext fun _ => by
    simp [toRealVec, toReal_one]
  rw [h1, Real.MatExp.scaleConj]
  simp


/-- The next start `ν V D̃ e₁` rounded up is within the window's error at `L`, plus the ball's
`|ν| r Σ ‖v_l‖₂`, plus the rounding's gap, of the true state. -/
private theorem LinearSys.aux_next {k : ℕ} (p : ℕ) (M : Mat ℝ n n) (V : Mat 𝕋 n (k + 1))
    (D : Mat 𝕋 (k + 1) (k + 1)) (ν rD : 𝕋) {Hr : Mat ℝ (k + 1) (k + 1)} {L X : ℝ} {v : Vec ℝ n}
    (hball : ‖exp (L • Hr) - toRealMat D‖ ≤ toReal rD)
    (hin : ‖exp (L • M) *ᵥ v - toReal ν • (toRealMat V *ᵥ (exp (L • Hr) *ᵥ
      fun l => if l.val = 0 then 1 else 0))‖₂ ≤ X) : -- --- CONCL ---
    ‖exp (L • M) *ᵥ v - toRealVec (fun i => Interval.mulHi ν ν (dotDown (V i) fun l => D l 0)
        (dotUp (V i) fun l => D l 0))‖₂ ≤
      X + (toReal (mulUp (mulUp (absolute ν) rD) (sumUp fun l => normUp p fun i => V i l)) +
        toReal (normUp p fun i => subUp (Interval.mulHi ν ν (dotDown (V i) fun l => D l 0)
          (dotUp (V i) fun l => D l 0)) (Interval.mulLo ν ν (dotDown (V i) fun l => D l 0)
            (dotUp (V i) fun l => D l 0)))) := by -- --- PROOF ---
  set e₁ : Vec ℝ (k + 1) := fun l => if l.val = 0 then 1 else 0 with he₁
  set d : Vec ℝ (k + 1) := fun l => toReal (D l 0) with hd
  set lo := fun i => Interval.mulLo ν ν (dotDown (V i) fun l => D l 0)
    (dotUp (V i) fun l => D l 0) with hlo
  set hi := fun i => Interval.mulHi ν ν (dotDown (V i) fun l => D l 0)
    (dotUp (V i) fun l => D l 0) with hhi
  set y := toReal ν • (toRealMat V *ᵥ d) with hy
  have hrD0 : 0 ≤ toReal rD := le_trans (norm_nonneg _) hball
  -- `|ψ(L)_l - D̃_l0| ≤ r`
  have hδ : ∀ l, |(exp (L • Hr) *ᵥ e₁ - d) l| ≤ toReal rD := fun l => by
    have he : e₁ = Pi.single 0 1 := LinearSys.aux_e₁ k
    have hdd : d = toRealMat D *ᵥ e₁ := by
      rw [he, mulVec_single_one]; rfl
    rw [hdd, ← sub_mulVec]
    have hn : ‖e₁‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
      rw [he]; by_cases h : j = 0 <;> simp [h]
    calc |((exp (L • Hr) - toRealMat D) *ᵥ e₁) l|
        ≤ ‖(exp (L • Hr) - toRealMat D) *ᵥ e₁‖ :=
          (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l)
      _ ≤ ‖exp (L • Hr) - toRealMat D‖ * ‖e₁‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ toReal rD * 1 := mul_le_mul hball hn (norm_nonneg _) hrD0
      _ = toReal rD := mul_one _
  -- `‖ν V δ‖₂ ≤ |ν| r Σ ‖v_l‖₂`
  have hcol : ∀ δ : Vec ℝ (k + 1), toRealMat V *ᵥ δ = ∑ l, δ l • fun i => toReal (V i l) :=
    fun δ => by funext i; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm, toRealMat]
  have hS0 : 0 ≤ toReal (sumUp fun l => normUp p fun i => V i l) :=
    le_trans (Finset.sum_nonneg fun l _ => norm₂_nonneg (fun i => toReal (V i l)))
      (le_trans (Finset.sum_le_sum fun l _ => norm₂_le_normUp p fun i => le_rfl)
        (sum_le_sumUp (fun l : Fin (k + 1) => normUp p fun i => V i l)))
  have hstart : ‖toReal ν • (toRealMat V *ᵥ (exp (L • Hr) *ᵥ e₁ - d))‖₂ ≤
      toReal (mulUp (mulUp (absolute ν) rD) (sumUp fun l => normUp p fun i => V i l)) := by
    rw [norm₂_smul, hcol]
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans (norm₂_sum_le _ _)
      (Finset.sum_le_sum fun l _ => le_of_eq (norm₂_smul _ _))) (abs_nonneg _)) ?_
    have h1 : ∑ l, |(exp (L • Hr) *ᵥ e₁ - d) l| * ‖fun i => toReal (V i l)‖₂ ≤
        toReal rD * toReal (sumUp fun l => normUp p fun i => V i l) := by
      refine le_trans (Finset.sum_le_sum fun l _ => mul_le_mul (hδ l)
        (norm₂_le_normUp p fun i => le_rfl) (norm₂_nonneg _) hrD0) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_le_sumUp _) hrD0
-- then the rounding of `|ν| r Σ ‖v_l‖₂`
    have h2 := mul_le_mulUp (mulUp (absolute ν) rD) (sumUp fun l => normUp p fun i => V i l)
    have h3 := mul_le_mulUp (absolute ν) rD
    rw [toReal_absolute] at h3
    calc |toReal ν| * ∑ l, |(exp (L • Hr) *ᵥ e₁ - d) l| * ‖fun i => toReal (V i l)‖₂
        ≤ |toReal ν| * (toReal rD * toReal (sumUp fun l => normUp p fun i => V i l)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |toReal ν| * toReal rD * toReal (sumUp fun l => normUp p fun i => V i l) := by ring
      _ ≤ toReal (mulUp (absolute ν) rD) * toReal (sumUp fun l => normUp p fun i => V i l) :=
          mul_le_mul_of_nonneg_right h3 hS0
      _ ≤ _ := h2
  -- the rounding of `ν V D̃ e₁`
  have hround : ‖y - toRealVec hi‖₂ ≤ toReal (normUp p fun i => subUp (hi i) (lo i)) := by
    refine norm₂_le_normUp p fun i => ?_
    have hyi : y i = toReal ν * ∑ l, toReal (V i l) * toReal (D l 0) := by
      simp [hy, hd, mulVec, dotProduct, toRealMat]
    have hc := Interval.mul_between_corners (le_refl (toReal ν)) le_rfl
      (dotDown_le (V i) fun l => D l 0) (le_dotUp (V i) fun l => D l 0)
    rw [← hyi] at hc
    have hsub := sub_le_subUp (hi i) (lo i)
    have hab := le_abs_self (toReal (subUp (hi i) (lo i)))
    simp only [Pi.sub_apply, toRealVec]
    rw [abs_le]
    exact ⟨by linarith [hc.1, hc.2], by linarith [hc.1, hc.2]⟩
  have hsplit : exp (L • M) *ᵥ v - toRealVec hi =
      (exp (L • M) *ᵥ v - toReal ν • (toRealMat V *ᵥ (exp (L • Hr) *ᵥ e₁))) +
      toReal ν • (toRealMat V *ᵥ (exp (L • Hr) *ᵥ e₁ - d)) + (y - toRealVec hi) := by
    rw [hy, mulVec_sub, smul_sub]; abel
  rw [hsplit]
  refine le_trans (norm₂_add_le _ _) ?_
  refine le_trans (add_le_add (norm₂_add_le _ _) le_rfl) ?_
  linarith

/-- One window from a start within `C` of the true state `v`: the window's Gershgorin error and the
local error of its own start at every time of it, and the next start within `C'` of `v`'s and
within the transition error of `x`'s. -/
private theorem LinearSys.aux_window (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋) (At : Mat 𝕋 n n)
    (Δt₀ : 𝕋) (x : Vec 𝕋 n) (C : 𝕋) (k m : ℕ) {W : LinearSys.VerifyKrylovWindow 𝕋 n}
    {x' : Vec 𝕋 n} {C' L loc ε : 𝕋}
    (hW : LinearSys.step_verifyKrylovWindowFloat p q εb At Δt₀ x C k m =
      some (W, x', C', L, loc, ε))
    (v : Vec ℝ n) (hv : ‖v - toRealVec x‖₂ ≤ toReal C) : -- --- CONCL ---
    let ψ : ℝ → Vec ℝ n := fun τ => toReal W.ν • (toRealMat W.V *ᵥ
      (exp (τ • toRealMat W.H) *ᵥ fun l => if l.val = 0 then 1 else 0))
    W.steps = m ∧ 0 ≤ toReal Δt₀ ∧ toReal L = (m : ℝ) * toReal Δt₀ ∧
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ (m : ℝ) * toReal Δt₀ →
      ‖exp (τ • toRealMat At) *ᵥ v - ψ τ‖₂ ≤ toReal W.err) ∧
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ (m : ℝ) * toReal Δt₀ →
      ‖exp (τ • toRealMat At) *ᵥ toRealVec x - ψ τ‖₂ ≤ toReal loc) ∧
    ‖exp (((m : ℝ) * toReal Δt₀) • toRealMat At) *ᵥ v - toRealVec x'‖₂ ≤ toReal C' ∧
    ‖exp (((m : ℝ) * toReal Δt₀) • toRealMat At) *ᵥ toRealVec x - toRealVec x'‖₂ ≤
      toReal ε := by -- --- PROOF ---
  intro ψ
  cases k with
  | zero => simp [LinearSys.step_verifyKrylovWindowFloat] at hW
  | succ k =>
  rw [LinearSys.step_verifyKrylovWindowFloat] at hW
  dsimp only at hW
  split_ifs at hW with hok
  rw [Bool.not_eq_true', Bool.not_eq_false] at hok
-- name the subspace, the scale and the length; read the checks
  have hH := Krylov.arnoldiFloat_hessenberg p εb At x (normUp p x) (k + 1)
  generalize Krylov.arnoldiFloat p εb At x (normUp p x) (k + 1) = st at hok hW hH
  generalize hν : normUp p x = ν at hok hW
  generalize hLd : nsmulUp m Δt₀ = L at hok hW
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hex, hΔ0⟩, hcap⟩, hgr⟩ := hok
  have hΔ : 0 ≤ toReal Δt₀ := by simpa [toReal_zero] using toReal_le_of_le hΔ0
  have hL : toReal L = (m : ℝ) * toReal Δt₀ := by
    have h1 := le_nsmulUp m Δt₀
    have h2 := nsmulDown_le m Δt₀
    have h3 := toReal_le_of_le hex
    rw [hLd] at h1
    linarith
  rcases hb : MatExp.expBallFloat (fun i j : Fin (k + 1) => st.2 i j) (fun _ => FloatOps.one) L
    with _ | ⟨D, rD⟩
  · rw [hb] at hW; cases hW
  rw [hb] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hW
  -- the growth `e^{τ μ_A} ≤ g` for `τ ≤ L`
  set μA := Krylov.quadBoundUp At with hμA
  set g := expUp 30 (mulUp L (maximum μA FloatOps.zero)) with hg
  have hgrow : ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal L → ∀ y : Vec ℝ n,
      ‖exp (τ • toRealMat At) *ᵥ y‖₂ ≤ toReal g * ‖y‖₂ := by
    intro τ h0 h1 y
    refine le_trans (LinearSys.aux_growth_norm _ (Krylov.quad_le_quadBoundUp At) y h0)
      (mul_le_mul_of_nonneg_right ?_ (norm₂_nonneg _))
    have hexp := le_expUp 30 (mulUp L (maximum μA FloatOps.zero))
      (le_trans (toReal_le_of_le hgr) (le_trans (LinearSys.aux_doublings 29) (by norm_num)))
    refine le_trans (Real.exp_le_exp.mpr ?_) hexp
    have hm : toReal μA ≤ toReal (maximum μA FloatOps.zero) := by
      rw [toReal_maximum]; exact le_max_left _ _
    have hm0 : 0 ≤ toReal (maximum μA FloatOps.zero) := by
      rw [toReal_maximum, toReal_zero]; exact le_max_right _ _
    calc toReal μA * τ ≤ toReal (maximum μA FloatOps.zero) * τ :=
          mul_le_mul_of_nonneg_right hm h0
      _ ≤ toReal L * toReal (maximum μA FloatOps.zero) := by nlinarith
      _ ≤ _ := mul_le_mulUp _ _
  -- the local error of the subspace of `x`
  let ψV : ℝ → Vec ℝ n := fun τ => toReal ν • (toRealMat (fun i (j : Fin (k + 1)) =>
    (st.1 j)[i]) *ᵥ (exp (τ • toRealMat (fun i j : Fin (k + 1) => st.2 i j)) *ᵥ
      fun l => if l.val = 0 then 1 else 0))
  have hloc : ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal L → ‖exp (τ • toRealMat At) *ᵥ toRealVec x - ψV τ‖₂ ≤
        toReal (Krylov.errorBoundFloat p q μA
          (fun j => Krylov.residualNormFloat p At st.1 st.2 j) x ν st.1 st.2 (k + 1) L) := by
    intro τ h0 h1
    show ‖_ - toReal ν • (_ *ᵥ (_ *ᵥ fun l : Fin (k + 1) => if l.val = 0 then 1 else 0))‖₂ ≤ _
    rw [LinearSys.aux_e₁]
    have := Krylov.error_le_errorBoundFloat p q At x ν st.1 st.2 k L μA
      (fun j => Krylov.residualNormFloat p At st.1 st.2 j) hq (fun i j hij => hH i j hij)
      (fun y => Krylov.quad_le_quadBoundUp At y)
      (fun j _ => Krylov.residual_le_residualNormFloat p At st.1 st.2 j) (by rw [hL]; positivity)
      hcap τ ⟨h0, h1⟩
    exact this
  set loc := Krylov.errorBoundFloat p q μA
    (fun j => Krylov.residualNormFloat p At st.1 st.2 j) x ν st.1 st.2 (k + 1) L
  have hgC : toReal g * toReal C ≤ toReal (mulUp g C) := mul_le_mulUp _ _
  have hg0 : 0 ≤ toReal g := le_trans (Real.exp_pos _).le (le_expUp 30 _
    (le_trans (toReal_le_of_le hgr) (le_trans (LinearSys.aux_doublings 29) (by norm_num))))
  -- inside the window: the carried start error plus the local one
  have hin : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (m : ℝ) * toReal Δt₀ →
      ‖exp (τ • toRealMat At) *ᵥ v - ψV τ‖₂ ≤ toReal g * toReal C + toReal loc := by
    intro τ h0 h1
    rw [← hL] at h1
    have hsplit : exp (τ • toRealMat At) *ᵥ v - ψV τ = exp (τ • toRealMat At) *ᵥ (v - toRealVec x) +
        (exp (τ • toRealMat At) *ᵥ toRealVec x - ψV τ) := by
      rw [mulVec_sub]; abel
    rw [hsplit]
    refine le_trans (norm₂_add_le _ _) (add_le_add ?_ (hloc τ h0 h1))
    exact le_trans (hgrow τ h0 h1 _) (mul_le_mul_of_nonneg_left hv hg0)
  have hloc' : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (m : ℝ) * toReal Δt₀ →
      ‖exp (τ • toRealMat At) *ᵥ toRealVec x - ψV τ‖₂ ≤ toReal loc := fun τ h0 h1 =>
    hloc τ h0 (by rw [hL]; exact h1)
  refine ⟨rfl, hΔ, hL, fun τ h0 h1 => le_trans (hin τ h0 h1)
    (le_trans (add_le_add hgC le_rfl) (add_le_addUp _ _)), hloc', ?_⟩
-- the next start, from the window at `L`
  have hball := MatExp.norm_scaleConj_exp_sub_le_expBallFloat (fun i j : Fin (k + 1) => st.2 i j)
    (s := fun _ => FloatOps.one) (fun _ => by rw [toReal_one]; exact one_pos)
    (by rw [hL]; positivity) (D, rD) (Option.mem_def.mpr hb)
  rw [LinearSys.aux_scaleConj_one] at hball
  have h1 := hin (toReal L) (by rw [hL]; positivity) hL.le
  have h2 := hloc (toReal L) (by rw [hL]; positivity) le_rfl
  rw [← hL]
  have hn := LinearSys.aux_next p (toRealMat At) (fun i (j : Fin (k + 1)) => (st.1 j)[i]) D ν rD
    hball h1
  have hn' := LinearSys.aux_next p (toRealMat At) (fun i (j : Fin (k + 1)) => (st.1 j)[i]) D ν rD
    hball h2
  refine ⟨le_trans hn (le_trans (add_le_add (le_trans (add_le_add hgC le_rfl)
    (add_le_addUp _ _)) (add_le_addUp _ _)) (add_le_addUp _ _)), ?_⟩
  exact le_trans hn' (le_trans (add_le_add le_rfl (add_le_addUp _ _)) (add_le_addUp _ _))

/-- `w' e^{tA} = e^{tA'} w`. -/
private theorem LinearSys.aux_vecMul_exp (A : Mat ℝ n n) (t : ℝ) (w : Vec ℝ n) :
    w ᵥ* exp (t • A) = exp (t • Aᵀ) *ᵥ w := by
  rw [← Matrix.transpose_smul, Matrix.exp_transpose, Matrix.mulVec_transpose]

/-- The element `j` of `l ++ [a]` below `l`'s length is `l`'s. -/
private theorem LinearSys.aux_getD_left {α : Type} (l : List α) (a d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [a]).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- The element of `l ++ [a]` at `l`'s length is `a`. -/
private theorem LinearSys.aux_getD_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

/-- `e^{(a + b)M} = e^{bM} e^{aM}`. -/
private theorem LinearSys.aux_exp_add (M : Mat ℝ n n) (a b : ℝ) :
    exp ((a + b) • M) = exp (b • M) * exp (a • M) := by
  have hc : Commute (b • M) (a • M) := ((Commute.refl _).smul_left b).smul_right a
  rw [add_comm a b, add_smul]
  exact exp_add_of_commute hc

/-- The history of the windows before: float starts `ws` from `wr`, each within its transition
error of the one before carried over its length, the lengths summing to `S Δt₀`. -/
private def LinearSys.aux_history (M : Mat ℝ n n) (wr : Vec ℝ n) (Δt₀ : 𝕋) (S : ℕ)
    (x : Vec 𝕋 n) (Δts εs : List 𝕋) (ws : ℕ → Vec ℝ n) : Prop :=
  Δts.length = εs.length ∧ ws 0 = wr ∧ ws Δts.length = toRealVec x ∧
  (∀ j < Δts.length, ‖exp (toReal (Δts.getD j zero) • M) *ᵥ ws j - ws (j + 1)‖₂ ≤
    toReal (εs.getD j zero)) ∧
  ∑ j ∈ Finset.range Δts.length, toReal (Δts.getD j zero) = (S : ℝ) * toReal Δt₀

/-- The Lyapunov carry of window `N = Δts.length`: within its bound of the true state. -/
private theorem LinearSys.aux_weighted (p q : ℕ) (At P Lc : Mat 𝕋 n n) (a : 𝕋) (wr : Vec ℝ n)
    (Δt₀ : 𝕋) (S : ℕ) (x : Vec 𝕋 n) (Δts εs : List 𝕋) (ws : ℕ → Vec ℝ n) (L loc : 𝕋)
    (ψ : ℝ → Vec ℝ n)
    (hH : LinearSys.aux_history (toRealMat At) wr Δt₀ S x Δts εs ws)
    (hok : Krylov.windowErrorOkFloat q (Krylov.lyapunovCertificateFloat At P Lc a)
      (fun j => (Δts ++ [L]).getD j zero) Δts.length = true)
    (hin : ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal L →
      ‖exp (τ • toRealMat At) *ᵥ toRealVec x - ψ τ‖₂ ≤ toReal loc) : -- --- CONCL ---
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal L →
      ‖exp (τ • toRealMat At) *ᵥ (exp (((S : ℝ) * toReal Δt₀) • toRealMat At) *ᵥ wr) - ψ τ‖₂ ≤
        toReal (Krylov.windowErrorBoundFloat p q (Krylov.lyapunovCertificateFloat At P Lc a)
          (fun j => (Δts ++ [L]).getD j zero) (fun j => (εs ++ [loc]).getD j zero)
            Δts.length) := by -- --- PROOF ---
  obtain ⟨hlen, h0, hN, hloc, hsum⟩ := hH
  set N := Δts.length
  -- the true states at the window starts
  let v : ℕ → Vec ℝ n := fun j => exp ((∑ i ∈ Finset.range j,
    toReal ((Δts ++ [L]).getD i zero)) • toRealMat At) *ᵥ wr
  have hvN : v N = exp (((S : ℝ) * toReal Δt₀) • toRealMat At) *ᵥ wr := by
    show exp (_ • _) *ᵥ wr = _
    rw [← hsum]
    congr 3
    exact Finset.sum_congr rfl fun j hj =>
      by rw [LinearSys.aux_getD_left _ _ _ (Finset.mem_range.mp hj)]
  rw [← hvN]
  refine Krylov.windowErrorBoundFloat_sound p q At P Lc a _ _ N (toReal L) hok v ws
    (fun j _ => ws (j + 1)) ψ (fun j _ => ?_) (fun j _ => rfl) ?_ (fun j hj => ?_) ?_
  · -- `v` steps by the lengths
    show exp (_ • _) *ᵥ wr = _ *ᵥ (exp (_ • _) *ᵥ wr)
    rw [Finset.sum_range_succ, LinearSys.aux_exp_add, mulVec_mulVec]
  · simp [v, h0]
  · -- the transitions before
    rw [LinearSys.aux_getD_left _ _ _ hj, LinearSys.aux_getD_left _ _ _ (hlen ▸ hj)]
    exact hloc j hj
  · -- inside this window
    intro τ h0' h1'
    rw [hN, hlen, LinearSys.aux_getD_last]
    exact hin τ h0' h1'

/-- The windows of the plan from a start within `C` of `e^{S Δt₀ A'} w`, after a history, each
holding `w' e^{tA}` from its offset. -/
private theorem LinearSys.aux_loop (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋) (A : Mat 𝕋 n n) (Δt₀ : 𝕋)
    (wr : Vec ℝ n) (c : Option (Krylov.LyapunovCertificateFloat 𝕋))
    (hc : ∀ c' ∈ c, ∃ P Lc a,
      c' = Krylov.lyapunovCertificateFloat (fun i j => A j i) P Lc a) : -- --- CONCL ---
    ∀ (plan : List (ℕ × ℕ)) (x : Vec 𝕋 n) (C : 𝕋) (S : ℕ) (Δts εs : List 𝕋) (ws : ℕ → Vec ℝ n)
      (wins : List (LinearSys.VerifyKrylovWindow 𝕋 n)),
      LinearSys.aux_history (toRealMat A)ᵀ wr Δt₀ S x Δts εs ws →
      ‖exp (((S : ℝ) * toReal Δt₀) • (toRealMat A)ᵀ) *ᵥ wr - toRealVec x‖₂ ≤ toReal C →
      LinearSys.step_verifyKrylovWindowsLoopFloat p q εb (fun i j => A j i) Δt₀ c plan x C Δts
        εs = some wins →
      ∀ i (hi : i < wins.length) (τ : ℝ), 0 ≤ τ → τ ≤ (wins[i].steps : ℝ) * toReal Δt₀ →
        ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal wins[i].err ∧
          wr ᵥ* exp (((((S + ((wins.take i).map (·.steps)).sum : ℕ)) : ℝ) * toReal Δt₀ + τ) •
            toRealMat A) = toReal wins[i].ν • (toRealMat wins[i].V *ᵥ
              (exp (τ • toRealMat wins[i].H) *ᵥ fun l => if l.val = 0 then 1 else 0)) +
                e := by -- --- PROOF ---
  intro plan
  induction plan with
  | nil =>
    intro x C S Δts εs ws wins _ _ h i hi
    simp only [LinearSys.step_verifyKrylovWindowsLoopFloat, Option.some.injEq] at h
    subst h; simp at hi
  | cons km plan ih =>
-- the first window and the windows after it
  intro x C S Δts εs ws wins hH hx h
  obtain ⟨k, m⟩ := km
  rw [LinearSys.step_verifyKrylovWindowsLoopFloat] at h
  rcases hw : LinearSys.step_verifyKrylovWindowFloat p q εb (fun i j => A j i) Δt₀ x C k m with
    _ | ⟨W, x', C', L, loc, ε⟩
  · rw [hw] at h; cases h
  rw [hw] at h
  dsimp only at h
  generalize herr : LinearSys.step_verifyKrylovCarryFloat p q c Δts εs L loc W.err = err at h
  rcases hr : LinearSys.step_verifyKrylovWindowsLoopFloat p q εb (fun i j => A j i) Δt₀ c plan x'
    C' (Δts ++ [L]) (εs ++ [ε]) with _ | rest
  · rw [hr] at h; cases h
  rw [hr] at h
  simp only [Option.map_some, Option.some.injEq] at h
  subst h
-- the first window's facts, with `A'`
  have hAt : toRealMat (fun i j => A j i) = (toRealMat A)ᵀ := rfl
  obtain ⟨hsteps, hΔ, hL, hin, hown, hnext, htrans⟩ :=
    LinearSys.aux_window p q hq εb _ Δt₀ x C k m hw _ hx
  rw [hAt] at hin hown hnext htrans
  -- the window's error, the smaller carry where the certificate holds
  have hcarry : ∀ τ : ℝ, 0 ≤ τ → τ ≤ (m : ℝ) * toReal Δt₀ →
      ‖exp (τ • (toRealMat A)ᵀ) *ᵥ (exp (((S : ℝ) * toReal Δt₀) • (toRealMat A)ᵀ) *ᵥ wr) -
        toReal W.ν • (toRealMat W.V *ᵥ (exp (τ • toRealMat W.H) *ᵥ
          fun l => if l.val = 0 then 1 else 0))‖₂ ≤ toReal err := by
    intro τ h0 h1
    subst herr
    rcases c with _ | c
    · exact hin τ h0 h1
    unfold LinearSys.step_verifyKrylovCarryFloat
    dsimp only
    split_ifs with hok
    · obtain ⟨P, Lc, a, rfl⟩ := hc _ rfl
      refine Krylov.carryMinFloat_sound _ _ _ (hin τ h0 h1) ?_
      exact LinearSys.aux_weighted p q _ P Lc a wr Δt₀ S x Δts εs ws L loc _ hH hok
        (fun τ h0 h1 => hown τ h0 (by rw [← hL]; exact h1)) τ h0 (by rw [hL]; exact h1)
    · exact hin τ h0 h1
  -- window `0` is this one, window `i + 1` the rest's `i`
  intro i hi τ h0 h1
  cases i with
  | zero =>
    -- the carry's bound, at the offset `S Δt₀`
    dsimp only [List.getElem_cons_zero, List.take_zero, List.map_nil, List.sum_nil] at h1 ⊢
    rw [Nat.add_zero]
    refine ⟨_, hcarry τ h0 (by rw [← hsteps]; exact h1), ?_⟩
    rw [LinearSys.aux_vecMul_exp, LinearSys.aux_exp_add, ← mulVec_mulVec]
    exact (add_sub_cancel _ _).symm
  | succ i =>
    -- the next start within `C'`, at the offset `(S + m) Δt₀`
    have hx' : ‖exp ((((S + m : ℕ) : ℝ) * toReal Δt₀) • (toRealMat A)ᵀ) *ᵥ wr -
        toRealVec x'‖₂ ≤ toReal C' := by
      rw [show (((S + m : ℕ) : ℝ)) * toReal Δt₀ = (S : ℝ) * toReal Δt₀ + m * toReal Δt₀ by
        push_cast; ring, LinearSys.aux_exp_add, ← mulVec_mulVec]
      exact hnext
    -- the history with this window
    obtain ⟨hlen, h0w, hNw, hlocw, hsum⟩ := hH
    have hH' : LinearSys.aux_history (toRealMat A)ᵀ wr Δt₀ (S + m) x' (Δts ++ [L]) (εs ++ [ε])
        (fun j => if j = Δts.length + 1 then toRealVec x' else ws j) := by
      refine ⟨by simp [hlen], by simp [h0w], by simp, fun j hj => ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at hj
        dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rw [LinearSys.aux_getD_left _ _ _ hj, LinearSys.aux_getD_left _ _ _ (hlen ▸ hj),
            if_neg (show j ≠ Δts.length + 1 by omega),
            if_neg (show j + 1 ≠ Δts.length + 1 by omega)]
          exact hlocw j hj
        · -- this window's transition
          subst hj
          rw [LinearSys.aux_getD_last, if_neg (show Δts.length ≠ Δts.length + 1 by omega),
            if_pos rfl, hNw, hL]
          have hε : (εs ++ [ε]).getD Δts.length FloatOps.zero = ε := by
            rw [hlen, LinearSys.aux_getD_last]
          rw [hε]
          exact htrans
      · -- the lengths now sum to `(S + m) Δt₀`
        rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
          LinearSys.aux_getD_last, Finset.sum_congr rfl fun j hj => by
            rw [LinearSys.aux_getD_left _ _ _ (Finset.mem_range.mp hj)], hsum, hL]
        push_cast; ring
    -- the rest's window `i`, offset by this window's steps
    have := ih x' C' (S + m) _ _ _ rest hH' hx' hr i (by simpa using hi) τ h0
      (by simpa using h1)
    have hsum' : S + ((({ W with err := err } :: rest).take (i + 1)).map (·.steps)).sum =
        S + m + ((rest.take i).map (·.steps)).sum := by simp [hsteps, Nat.add_assoc]
    rw [hsum']
    exact this


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyKrylovWindowsFloat_sound (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋)
    (A : Mat 𝕋 n n) (w : Vec 𝕋 n) (Δt₀ : 𝕋) (plan : List (ℕ × ℕ))
    (cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋)) : -- --- CONCL ---
    ∀ wins ∈ LinearSys.verifyKrylovWindowsFloat p q εb A w Δt₀ plan cert,
      LinearSys.IsVerifyKrylovWindows (toRealMat A) (toRealVec w) (toReal Δt₀)
        wins := by -- --- PROOF ---
  intro wins h i hi τ h0 h1
  have hc : ∀ c' ∈ cert.map fun (P, L, a) =>
      Krylov.lyapunovCertificateFloat (fun i j => A j i) P L a,
      ∃ P L a, c' = Krylov.lyapunovCertificateFloat (fun i j => A j i) P L a := by
    intro c' hc'
    rcases cert with _ | ⟨P, L, a⟩
    · cases hc'
    · exact ⟨P, L, a, (Option.some.inj hc').symm⟩
  have hH : LinearSys.aux_history (toRealMat A)ᵀ (toRealVec w) Δt₀ 0 w [] [] fun _ => toRealVec w :=
    ⟨rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), by simp⟩
  have := LinearSys.aux_loop p q hq εb A Δt₀ (toRealVec w) _ hc plan w FloatOps.zero 0 [] [] _
    wins hH (by simp [toReal_zero, norm₂_zero]) h i hi τ h0 h1
  simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
