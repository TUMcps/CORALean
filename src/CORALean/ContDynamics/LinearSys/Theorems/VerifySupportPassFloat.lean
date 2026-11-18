module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportPassFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionInputFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyBoxDotDownFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyBoxDotUpFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyInputInnerFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyInputOuterFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.WeightedSumVecMulLe
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyCurvatureUpFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySupportDownFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySupportUpFloat
public import CORALean.Global.Float.Exp

@[expose] public section

/-!
# One pass of `LinearSys.verifySupportPassFloat` is sound

With `D = e^{AΔt}` and the exact rows `ℓ_q`, the steps keep: the weighted error of `ℓ̃_k` carried
`m` more steps is at most `Y acc_k` for every `k + m ≤ N`, and the stored upper distance bounds
`ℓ_q D^k x − d_q` over `X₀`. A step adds `ℓ̃_k (D − D̃) + (ℓ̃_k D̃ − ℓ̃_{k+1})`, of weighted norm
at most `δ_k` (`MatExp.norm_scaleConj_exp_sub_le_expBallFloat`), carried by `Y ≥ ‖S⁻¹ D^m S‖`.
Over `[t_k, t_{k+1}]`, `e^{tA} = (1 − λ) D^k + λ D^{k+1} + D^k F_σ` with `F_σ` in `F`
(`MatExp.expDiff_mem_verifyCorrectionStateFloat`), so a set flag holds `ℓ_q e^{tA} x < d_q`
there. A falsifying time point has a point of `X₀` above `d_q`.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `v` – float bound of the initial set's magnitudes
* `βX` – float scaled bound of `v`
* `κ` – float growth factor
* `μ` – float growth rate
* `ℓ₀` – float rows
* `E₀` – float errors of the rows
* `d` – float offsets
* `Δt` – step size
* `N` – steps
* `T` – horizon of the falsification
* `Lr` – exact rows

## Hypotheses
* `hs` – the scales are positive
* `hv` – `v` bounds `|c| + Σⱼ |gⱼ|`
* `hβX0` – `βX` is nonnegative
* `hβX` – `βX` bounds every `vᵢ / sᵢ`
* `hμ` – `‖S⁻¹ e^{tA} S‖ ≤ κ e^{tμ}` for `t ≥ 0`
* `hE₀` – the weighted error of each row is at most `E₀`

## Conclusion
* every verified step holds its halfspace over the step for all of `X₀`; a falsifying time point
  lies within `T` and a point of `X₀` violates its halfspace there
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m p r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- `e^{AΔt}` carried `k` times is the flow over `kΔt`. -/
private theorem LinearSys.aux_exp_pow (A : Mat ℝ n n) (Δt : ℝ) (k : ℕ) :
    exp (((k : ℝ) * Δt) • A) = exp (Δt • A) ^ k := by
  have h1 : ((k : ℝ) * Δt) • A = k • (Δt • A) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [h1]
  exact Matrix.exp_nsmul k _

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The weighted norm of a sum of row vectors is at most the sum of the weighted norms. -/
private theorem LinearSys.aux_weighted_add (s : Vec ℝ n) (hs : ∀ i, 0 ≤ s i) (e f : Vec ℝ n) :
    ∑ i, |(e + f) i| * s i ≤ ∑ i, |e i| * s i + ∑ i, |f i| * s i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (hs i)

omit [ToRat 𝕋] in
/-- `σ` doublings from one stay below `2^σ`. -/
private theorem LinearSys.aux_doublings_le (σ : ℕ) : -- --- CONCL ---
    toReal ((fun x : 𝕋 => addDown x x)^[σ] FloatOps.one) ≤ 2 ^ σ := by -- --- PROOF ---
  induction σ with
  | zero => simp [toReal_one]
  | succ σ ih =>
    rw [Function.iterate_succ_apply']
    refine le_trans (addDown_le_add _ _) ?_
    rw [pow_succ]
    linarith

omit [ToRat 𝕋] in
/-- `Y = max(1, κ e↑(a))` is at least `1` and bounds the weighted norm of `D^p` for every
`p ≤ N`. -/
private theorem LinearSys.aux_growth (A : Mat 𝕋 n n) {s : Vec 𝕋 n} {κ μ Δt a : 𝕋} {N : ℕ}
    (hΔt : 0 < toReal Δt)
    (hμ : ∀ t : ℝ, 0 ≤ t → ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤
      toReal κ * Real.exp (t * toReal μ))
    (hadef : a = mulUp (maximum μ FloatOps.zero) (mulUp (nsmulUp N FloatOps.one) Δt))
    (ha : le a (Nat.iterate (fun x => addDown x x) 29 FloatOps.one) = true) : -- --- CONCL ---
    1 ≤ toReal (maximum FloatOps.one (mulUp κ (expUp 30 a))) ∧ ∀ p ≤ N,
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • toRealMat A) ^ p)‖
        ≤ toReal (maximum FloatOps.one (mulUp κ (expUp 30 a))) := by -- --- PROOF ---
  have hμ0 : 0 ≤ toReal (maximum μ FloatOps.zero) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_right _ _
  have hNt : (N : ℝ) * toReal Δt ≤ toReal (mulUp (nsmulUp N FloatOps.one) Δt) := by
    have h1 := le_nsmulUp N (FloatOps.one : 𝕋)
    rw [toReal_one, mul_one] at h1
    exact le_trans (mul_le_mul_of_nonneg_right h1 hΔt.le) (mul_le_mulUp _ _)
  have ha' : toReal (maximum μ FloatOps.zero) * ((N : ℝ) * toReal Δt) ≤ toReal a :=
    hadef ▸ le_trans (mul_le_mul_of_nonneg_left hNt hμ0) (mul_le_mulUp _ _)
  have hexp : Real.exp (toReal a) ≤ toReal (expUp 30 a) := by
    refine le_expUp 30 a (le_trans (toReal_le_of_le ha) ?_)
    refine le_trans (LinearSys.aux_doublings_le 29) (le_of_eq ?_)
    norm_num
  -- `κ ≥ ‖I‖ ≥ 0` at `t = 0`
  have hκ : 0 ≤ toReal κ := by
    have h := hμ 0 le_rfl
    rw [zero_mul, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨by rw [toReal_maximum, toReal_one]; exact le_max_left _ _, fun p hp => ?_⟩
  rw [← LinearSys.aux_exp_pow, toReal_maximum]
  refine le_trans (hμ _ (by positivity)) (le_trans ?_ (le_max_right _ _))
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.mpr ?_) hexp) hκ)
    (mul_le_mulUp _ _)
  have hpN : (p : ℝ) * toReal Δt ≤ (N : ℝ) * toReal Δt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hΔt.le
  have hμle : toReal μ ≤ toReal (maximum μ FloatOps.zero) := by
    rw [toReal_maximum]; exact le_max_left _ _
  -- `p Δt μ ≤ N Δt μ⁺ ≤ a`
  calc (p : ℝ) * toReal Δt * toReal μ
      ≤ (p : ℝ) * toReal Δt * toReal (maximum μ FloatOps.zero) :=
        mul_le_mul_of_nonneg_left hμle (by positivity)
    _ ≤ (N : ℝ) * toReal Δt * toReal (maximum μ FloatOps.zero) :=
        mul_le_mul_of_nonneg_right hpN hμ0
    _ ≤ toReal a := by linarith

omit [ToRat 𝕋] in
/-- The error a step adds: `ℓ̃ (D − D̃)` and the gap of the stored `ℓ̃ D̃` rounded up. -/
private theorem LinearSys.aux_step_error {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i))
    {Dr : Mat ℝ n n} {D : Mat 𝕋 n n} {rD : 𝕋}
    (hD : ‖Real.MatExp.scaleConj (toRealVec s) (Dr - toRealMat D)‖ ≤ toReal rD)
    (ℓ : Vec 𝕋 n) : -- --- CONCL ---
    ∑ j, |(toRealVec ℓ ᵥ* Dr - toRealVec fun j => dotUp ℓ fun i => D i j) j| * toReal (s j)
      ≤ toReal (addUp (mulUp (sumUp fun j => mulUp (absolute (ℓ j)) (s j)) rD)
        (sumUp fun j => mulUp (subUp (dotUp ℓ fun i => D i j) (dotDown ℓ fun i => D i j)) (s j)))
    := by -- --- PROOF ---
  have hsplit : toRealVec ℓ ᵥ* Dr - (toRealVec fun j => dotUp ℓ fun i => D i j)
      = toRealVec ℓ ᵥ* (Dr - toRealMat D)
        + (toRealVec ℓ ᵥ* toRealMat D - toRealVec fun j => dotUp ℓ fun i => D i j) := by
    rw [Matrix.vecMul_sub]; abel
  rw [hsplit]
  refine le_trans (LinearSys.aux_weighted_add _ (fun i => (hs i).le) _ _)
    (le_trans (add_le_add ?_ ?_) (add_le_addUp _ _))
  · -- `ℓ̃ (D − D̃)`
    refine le_trans (Real.MatExp.weightedSum_vecMul_le hs _ _) (le_trans ?_ (mul_le_mulUp _ _))
    have hw : ∑ i, |toRealVec ℓ i| * toRealVec s i
        ≤ toReal (sumUp fun j => mulUp (absolute (ℓ j)) (s j)) := by
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
      have := mul_le_mulUp (absolute (ℓ j)) (s j)
      rwa [toReal_absolute] at this
    exact mul_le_mul hw hD (norm_nonneg _)
      (le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hs i).le) hw)
  · -- the rounding of `ℓ̃ D̃`
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    have h1 := dotDown_le ℓ fun i => D i j
    have h2 := le_dotUp ℓ fun i => D i j
    have h3 := sub_le_subUp (dotUp ℓ fun i => D i j) (dotDown ℓ fun i => D i j)
    have hy : (toRealVec ℓ ᵥ* toRealMat D) j = ∑ i, toReal (ℓ i) * toReal (D i j) := rfl
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (hs j).le) (mul_le_mulUp _ _)
    show |(toRealVec ℓ ᵥ* toRealMat D) j - toReal (dotUp ℓ fun i => D i j)| ≤ _
    rw [hy, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- Over `[t_k, t_{k+1}]`: `ℓ e^{tA} x = (1 − λ) ℓ D^k x + λ ℓ D^{k+1} x + ℓ D^k F_σ x`. -/
private theorem LinearSys.aux_interp (Ar : Mat ℝ n n) (h : ℝ) (k : ℕ) (t : ℝ)
    (ℓ x : Vec ℝ n) : -- --- CONCL ---
    ℓ ⬝ᵥ (exp (t • Ar) *ᵥ x)
      = (1 - (t - k * h) / h) * ((ℓ ᵥ* exp (h • Ar) ^ k) ⬝ᵥ x)
        + (t - k * h) / h * ((ℓ ᵥ* exp (h • Ar) ^ (k + 1)) ⬝ᵥ x)
        + (ℓ ᵥ* exp (h • Ar) ^ k) ⬝ᵥ ((exp ((t - k * h) • Ar) - 1
          - ((t - k * h) / h) • (exp (h • Ar) - 1)) *ᵥ x) := by -- --- PROOF ---
  have hsplit : t • Ar = ((k : ℝ) * h) • Ar + (t - k * h) • Ar := by
    rw [← add_smul]; ring_nf
  have hcomm : Commute (((k : ℝ) * h) • Ar) ((t - k * h) • Ar) :=
    ((Commute.refl Ar).smul_left _).smul_right _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, LinearSys.aux_exp_pow, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec, pow_succ, ← Matrix.vecMul_vecMul]
  set u := ℓ ᵥ* exp (h • Ar) ^ k
  rw [← dotProduct_mulVec u (exp (h • Ar)) x]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  ring


omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The step's bound, combined: the two ends weighted by `λ`, the curvature terms and the input. -/
private theorem LinearSys.aux_combine {x0 x1 c0 wl D a0 a1 cu cb gu gb zs cov lam : ℝ}
    (h0 : x0 + c0 - D ≤ a0) (h1 : x1 + (c0 + wl) - D ≤ a1) (hcu : cu ≤ cb) (hgu : gu ≤ gb)
    (hzs : zs ≤ cov) (hlt : max a0 a1 + cb + gb + cov < 0) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : -- --- CONCL ---
    (1 - lam) * x0 + lam * x1 + cu + (lam * wl + gu) + c0 + zs < D := by -- --- PROOF ---
  have k0 := mul_le_mul_of_nonneg_left (le_trans h0 (le_max_left a0 a1)) (by linarith : 0 ≤ 1 - lam)
  have k1 := mul_le_mul_of_nonneg_left (le_trans h1 (le_max_right a0 a1)) hl0
  nlinarith


/-- Row `q` holds over step `i` of length `h` for every point of `X₀` and every input: its
constant part (`u₀`, `w = (∫₀ʰ e^{sA} ds) u₀`) and one varying contribution per step from `Z`. -/
private def LinearSys.aux_holdsOn (Ar : Mat ℝ n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Lr : Fin r → Vec ℝ n) (d : Vec 𝕋 r) (u0v wv : Vec ℝ n) (Z : Set (Vec ℝ n)) (h : ℝ) (i : ℕ)
    (q : Fin r) : Prop :=
  ∀ t : ℝ, i * h ≤ t → t ≤ (i + 1) * h → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
    ∀ zs : ℕ → Vec ℝ n, (∀ j < i + 1, zs j ∈ Z) →
    Lr q ⬝ᵥ (exp (t • Ar) *ᵥ (toRealVec c + toRealMat G *ᵥ b))
      + (Lr q ᵥ* exp (h • Ar) ^ i) ⬝ᵥ (Real.MatExp.expIntegral Ar (t - i * h) *ᵥ u0v)
      + ∑ j ∈ Finset.range i, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ wv
      + ∑ j ∈ Finset.range (i + 1), (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ zs j < toReal (d q)

/-- Row `q` is violated at `t_k = k h` by a point of `X₀` and an input: its constant part and one
varying contribution per step from `Z`. -/
private abbrev LinearSys.aux_violatedAt (Ar : Mat ℝ n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Lr : Fin r → Vec ℝ n) (d : Vec 𝕋 r) (wv : Vec ℝ n) (Z : Set (Vec ℝ n)) (h : ℝ) (k : ℕ)
    (q : Fin r) : Prop :=
  ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ ∃ zs : ℕ → Vec ℝ n, (∀ j < k, zs j ∈ Z) ∧
    toReal (d q) < Lr q ⬝ᵥ (exp (((k : ℝ) * h) • Ar) *ᵥ (toRealVec c + toRealMat G *ᵥ b))
      + ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ wv
      + ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ zs j

/-- What the steps carry to `t_k = k h`: the rows' weighted errors, the upper distances, and the
input's sums over the steps before (`ℓ' w` up and down, the outer and the inner support). -/
private abbrev LinearSys.aux_stepsInv (s c : Vec 𝕋 n) (G : Mat 𝕋 n m) (Ar : Mat ℝ n n)
    (Lr : Fin r → Vec ℝ n) (d : Vec 𝕋 r) (wv : Vec ℝ n) (Z : Set (Vec ℝ n)) (h : ℝ) (Y : 𝕋)
    (N k : ℕ) (ℓ : Mat 𝕋 r n) (acc aff cw cwd cov cin : Vec 𝕋 r) : Prop :=
  (∀ q p, k + p ≤ N → ∑ i, |((Lr q ᵥ* exp (h • Ar) ^ k - toRealVec (ℓ q)) ᵥ* exp (h • Ar) ^ p) i|
      * toReal (s i) ≤ toReal Y * toReal (acc q)) ∧
  (∀ q (b : Fin m → ℝ), (∀ j, |b j| ≤ 1) → (Lr q ᵥ* exp (h • Ar) ^ k) ⬝ᵥ (toRealVec c
      + toRealMat G *ᵥ b) + ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ wv - toReal (d q)
      ≤ toReal (aff q)) ∧
  (∀ q, ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ wv ≤ toReal (cw q)) ∧
  (∀ q, toReal (cwd q) ≤ ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ wv) ∧
  (∀ q (zs : ℕ → Vec ℝ n), (∀ j < k, zs j ∈ Z) →
    ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ zs j ≤ toReal (cov q)) ∧
  ∀ q, ∃ zs : ℕ → Vec ℝ n, (∀ j < k, zs j ∈ Z) ∧
    toReal (cin q) ≤ ∑ j ∈ Finset.range k, (Lr q ᵥ* exp (h • Ar) ^ j) ⬝ᵥ zs j

/-- The curvature term bounds `ℓ (e^{τA} − I − (τ/Δt)(D − I)) x` over a step, for every direction
within its error. -/
private def LinearSys.aux_curvBound (s c : Vec 𝕋 n) (G : Mat 𝕋 n m) (wc : Interval (Vec 𝕋 n))
    (WG : Interval (Mat 𝕋 n m)) (wr : Vec 𝕋 n) (βF : 𝕋) (Ar : Mat ℝ n n) (h : ℝ) : Prop :=
  ∀ (ℓr : Vec ℝ n) (ℓ : Vec 𝕋 n) (E : 𝕋),
    ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E → ∀ τ : ℝ, 0 ≤ τ → τ ≤ h →
    ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
    ℓr ⬝ᵥ ((exp (τ • Ar) - 1 - (τ / h) • (exp (h • Ar) - 1)) *ᵥ (toRealVec c + toRealMat G *ᵥ b))
      ≤ toReal (LinearSys.verifyCurvatureUpFloat wc WG wr βF ℓ E)

/-- The input's terms bound, for every direction within its error: `ℓ' w` from above and below,
`ℓ' z` over `Z` from above, some `ℓ' z` from below, and `ℓ' (∫₀^τ − (τ/h)∫₀^h) u₀` over a step. -/
private def LinearSys.aux_inputBound (s : Vec 𝕋 n) (I : LinearSys.VerifyInputSolution 𝕋 n p)
    (g : Interval (Mat 𝕋 n 1)) (βw βg βU : 𝕋) (u0v wv : Vec ℝ n) (Z : Set (Vec ℝ n))
    (Ar : Mat ℝ n n) (h : ℝ) : Prop :=
  ∀ (ℓr : Vec ℝ n) (ℓ : Vec 𝕋 n) (E : 𝕋),
    ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E →
    (ℓr ⬝ᵥ wv ≤ toReal (LinearSys.step_verifySupportInputFloat I g βw βg βU ℓ E).1 ∧
      toReal (LinearSys.step_verifySupportInputFloat I g βw βg βU ℓ E).2.1 ≤ ℓr ⬝ᵥ wv) ∧
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ h → ℓr ⬝ᵥ ((Real.MatExp.expIntegral Ar τ
      - (τ / h) • Real.MatExp.expIntegral Ar h) *ᵥ u0v)
        ≤ toReal (LinearSys.step_verifySupportInputFloat I g βw βg βU ℓ E).2.2.1) ∧
    (∀ z ∈ Z, ℓr ⬝ᵥ z ≤ toReal (LinearSys.step_verifySupportInputFloat I g βw βg βU ℓ E).2.2.2.1) ∧
    ∃ z ∈ Z, toReal (LinearSys.step_verifySupportInputFloat I g βw βg βU ℓ E).2.2.2.2 ≤ ℓr ⬝ᵥ z

/-- The steps keep the invariant: the carried errors, the distances, the input's sums, the flags
so far. -/
private theorem LinearSys.aux_steps {s c : Vec 𝕋 n} {G : Mat 𝕋 n m} {βX : 𝕋}
    {wc : Interval (Vec 𝕋 n)} {WG : Interval (Mat 𝕋 n m)} {wr : Vec 𝕋 n} {βF : 𝕋}
    {I : LinearSys.VerifyInputSolution 𝕋 n p} {g : Interval (Mat 𝕋 n 1)} {βw βg βU : 𝕋}
    {D : Mat 𝕋 n n} {rD Y : 𝕋} {d : Vec 𝕋 r} {Δt : 𝕋} {T : ℚ} {Ar : Mat ℝ n n}
    {Lr : Fin r → Vec ℝ n} {N : ℕ} {u0v wv : Vec ℝ n} {Z : Set (Vec ℝ n)}
    (hs : ∀ i, 0 < toReal (s i)) (hβX0 : 0 ≤ toReal βX) (hΔt : 0 < toReal Δt) (hY0 : 0 ≤ toReal Y)
    (hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i))
    (hY : ∀ p ≤ N, ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • Ar) ^ p)‖ ≤ toReal Y)
    (hD : ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • Ar) - toRealMat D)‖ ≤ toReal rD)
    (hcurv : LinearSys.aux_curvBound s c G wc WG wr βF Ar (toReal Δt))
    (hinp : LinearSys.aux_inputBound s I g βw βg βU u0v wv Z Ar (toReal Δt))
    (hwv : wv = Real.MatExp.expIntegral Ar (toReal Δt) *ᵥ u0v)
    (fuel k : ℕ) (ℓ : Mat 𝕋 r n) (acc aff cw cwd cov cin : Vec 𝕋 r) (flags : List (Fin r → Bool))
    (hkN : k + fuel = N) (hlen : flags.length = k)
    (hinv : LinearSys.aux_stepsInv s c G Ar Lr d wv Z (toReal Δt) Y N k ℓ acc aff cw cwd cov cin)
    (hflags : ∀ i (hi : i < flags.reverse.length) q, flags.reverse[i] q = true →
      LinearSys.aux_holdsOn Ar c G Lr d u0v wv Z (toReal Δt) i q) : -- --- CONCL ---
    (∀ fl, LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF I g βw βg βU D rD Y d Δt T
        k fuel ℓ acc aff cw cwd cov cin flags = .decided fl → fl.length = N ∧
      ∀ i (hi : i < fl.length) q, fl[i] q = true →
        LinearSys.aux_holdsOn Ar c G Lr d u0v wv Z (toReal Δt) i q)
    ∧ (∀ k' q, LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF I g βw βg βU D rD Y d
        Δt T k fuel ℓ acc aff cw cwd cov cin flags = .falsified k' q →
      (k' : ℚ) * ToRat.toRat Δt ≤ T ∧ 0 ≤ (k' : ℚ) * ToRat.toRat Δt ∧
      LinearSys.aux_violatedAt Ar c G Lr d wv Z (toReal Δt) k' q) := by -- --- PROOF ---
  set Dr := exp (toReal Δt • Ar)
  set X := fun b : Fin m → ℝ => toRealVec c + toRealMat G *ᵥ b
  induction fuel generalizing k ℓ acc aff cw cwd cov cin flags with
  | zero =>
    simp only [LinearSys.step_verifySupportStepsFloat, reduceCtorEq, false_imp_iff,
      implies_true, and_true]
    rintro fl ⟨⟩
    exact ⟨by rw [List.length_reverse]; omega, hflags⟩
  | succ fuel ih =>
    obtain ⟨hacc, haff, hcw, hcwd, hcov, hcin⟩ := hinv
    -- the new rows, errors and distances
    set ℓUp : Mat 𝕋 r n := fun q j => dotUp (ℓ q) fun i => D i j with hℓUp
    set δ : Vec 𝕋 r := fun q => addUp (mulUp (sumUp fun j => mulUp (absolute (ℓ q j)) (s j)) rD)
      (sumUp fun j => mulUp (subUp (ℓUp q j) (dotDown (ℓ q) fun i => D i j)) (s j)) with hδ
    set acc' : Vec 𝕋 r := fun q => addUp (acc q) (δ q) with hacc'
    set inp := fun q => LinearSys.step_verifySupportInputFloat I g βw βg βU (ℓ q)
      (mulUp Y (acc q)) with hinpdef
    set cw' : Vec 𝕋 r := fun q => addUp (cw q) (inp q).1 with hcw'
    set cwd' : Vec 𝕋 r := fun q => addDown (cwd q) (inp q).2.1 with hcwd'
    set cov' : Vec 𝕋 r := fun q => addUp (cov q) (inp q).2.2.2.1 with hcov'
    set cin' : Vec 𝕋 r := fun q => addDown (cin q) (inp q).2.2.2.2 with hcin'
    set aff' : Vec 𝕋 r := fun q => subUp (addUp (LinearSys.verifySupportUpFloat c G βX (ℓUp q)
      (mulUp Y (acc' q))) (cw' q)) (d q) with haff'
    set cwr := fun (k' : ℕ) (q : Fin r) => ∑ j ∈ Finset.range k', (Lr q ᵥ* Dr ^ j) ⬝ᵥ wv
    -- the invariant at `k + 1`
    have hacc1 : ∀ q p, k + 1 + p ≤ N →
        ∑ i, |((Lr q ᵥ* Dr ^ (k + 1) - toRealVec (ℓUp q)) ᵥ* Dr ^ p) i| * toReal (s i)
          ≤ toReal Y * toReal (acc' q) := by
      intro q p hp
      have he : (Lr q ᵥ* Dr ^ (k + 1) - toRealVec (ℓUp q)) ᵥ* Dr ^ p
          = (Lr q ᵥ* Dr ^ k - toRealVec (ℓ q)) ᵥ* Dr ^ (p + 1)
            + (toRealVec (ℓ q) ᵥ* Dr - toRealVec (ℓUp q)) ᵥ* Dr ^ p := by
        rw [pow_succ, pow_succ', ← Matrix.vecMul_vecMul, Matrix.sub_vecMul, Matrix.sub_vecMul,
          Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← mul_assoc,
          ← pow_succ, Matrix.vecMul_vecMul]
        abel
      rw [he]
      refine le_trans (LinearSys.aux_weighted_add _ (fun i => (hs i).le) _ _) ?_
      -- the carried error and the step's own, each carried by at most `Y`
      have h1 := hacc q (p + 1) (by omega)
      have hη : ∑ j, |(toRealVec (ℓ q) ᵥ* Dr - toRealVec (ℓUp q)) j| * toReal (s j)
          ≤ toReal (δ q) := LinearSys.aux_step_error hs hD (ℓ q)
      have h2 : ∑ j, |((toRealVec (ℓ q) ᵥ* Dr - toRealVec (ℓUp q)) ᵥ* Dr ^ p) j| * toReal (s j)
          ≤ toReal (δ q) * toReal Y :=
        le_trans (Real.MatExp.weightedSum_vecMul_le hs _ (Dr ^ p))
          (mul_le_mul hη (hY p (by omega)) (norm_nonneg _)
            (le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hs i).le) hη))
      have h4 : toReal Y * (toReal (acc q) + toReal (δ q)) ≤ toReal Y * toReal (acc' q) :=
        mul_le_mul_of_nonneg_left (add_le_addUp _ _) hY0
      linarith
    -- the error of the new rows and of the old ones
    have hE1 : ∀ q, ∑ i, |(Lr q ᵥ* Dr ^ (k + 1)) i - toReal (ℓUp q i)| * toReal (s i)
        ≤ toReal (mulUp Y (acc' q)) := by
      intro q
      have h := hacc1 q 0 (by omega)
      rw [pow_zero, Matrix.vecMul_one] at h
      exact le_trans h (mul_le_mulUp _ _)
    have hE0 : ∀ q, ∑ i, |(Lr q ᵥ* Dr ^ k) i - toReal (ℓ q i)| * toReal (s i)
        ≤ toReal (mulUp Y (acc q)) := by
      intro q
      have h := hacc q 0 (by omega)
      rw [pow_zero, Matrix.vecMul_one] at h
      exact le_trans h (mul_le_mulUp _ _)
    -- the input's sums at `k + 1`
    have hcwr : ∀ q, cwr (k + 1) q = cwr k q + (Lr q ᵥ* Dr ^ k) ⬝ᵥ wv := fun q =>
      Finset.sum_range_succ _ _
    have hcw1 : ∀ q, cwr (k + 1) q ≤ toReal (cw' q) := by
      intro q
      rw [hcwr]
      exact le_trans (add_le_add (hcw q) ((hinp _ _ _ (hE0 q)).1.1)) (add_le_addUp _ _)
    -- and from below
    have hcwd1 : ∀ q, toReal (cwd' q) ≤ cwr (k + 1) q := by
      intro q
      rw [hcwr]
      exact le_trans (addDown_le_add _ _) (add_le_add (hcwd q) ((hinp _ _ _ (hE0 q)).1.2))
    -- the outer sums: one more step's contribution
    have hcov1 : ∀ q (zs : ℕ → Vec ℝ n), (∀ j < k + 1, zs j ∈ Z) →
        ∑ j ∈ Finset.range (k + 1), (Lr q ᵥ* Dr ^ j) ⬝ᵥ zs j ≤ toReal (cov' q) := by
      intro q zs hzs
      rw [Finset.sum_range_succ]
      exact le_trans (add_le_add (hcov q zs fun j hj => hzs j (by omega))
        ((hinp _ _ _ (hE0 q)).2.2.1 _ (hzs k (by omega)))) (add_le_addUp _ _)
    -- the inner sums: one more step's witness appended
    have hcin1 : ∀ q, ∃ zs : ℕ → Vec ℝ n, (∀ j < k + 1, zs j ∈ Z) ∧
        toReal (cin' q) ≤ ∑ j ∈ Finset.range (k + 1), (Lr q ᵥ* Dr ^ j) ⬝ᵥ zs j := by
      intro q
      obtain ⟨zs, hzs, hle⟩ := hcin q
      obtain ⟨z, hz, hzle⟩ := (hinp _ _ _ (hE0 q)).2.2.2
      refine ⟨Function.update zs k z, fun j hj => ?_, ?_⟩
      · by_cases hjk : j = k
        · subst hjk; simpa using hz
        · rw [Function.update_of_ne hjk]; exact hzs j (by omega)
      · rw [Finset.sum_range_succ, Function.update_self]
        -- the earlier witnesses unchanged
        have hsame : ∑ j ∈ Finset.range k, (Lr q ᵥ* Dr ^ j) ⬝ᵥ Function.update zs k z j
            = ∑ j ∈ Finset.range k, (Lr q ᵥ* Dr ^ j) ⬝ᵥ zs j :=
          Finset.sum_congr rfl fun j hj => by
            rw [Function.update_of_ne (by simp at hj; omega)]
        rw [hsame]
        exact le_trans (addDown_le_add _ _) (add_le_add hle hzle)
    -- the distances at `k + 1`
    have haff1 : ∀ q (b : Fin m → ℝ), (∀ j, |b j| ≤ 1) →
        (Lr q ᵥ* Dr ^ (k + 1)) ⬝ᵥ X b + cwr (k + 1) q - toReal (d q) ≤ toReal (aff' q) := by
      intro q b hb
      have h := LinearSys.dotProduct_le_verifySupportUpFloat c G hβX0 hβ (ℓUp q) (hE1 q) hb
      refine le_trans ?_ (sub_le_subUp _ _)
      linarith [hcw1 q, add_le_addUp (LinearSys.verifySupportUpFloat c G βX (ℓUp q)
        (mulUp Y (acc' q))) (cw' q)]
    -- a set flag holds over the step
    have hflag : ∀ q, ltStrict (addUp (addUp (addUp (maximum (aff q) (aff' q))
        (LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (mulUp Y (acc q))))
        (inp q).2.2.1) (cov' q)) zero = true →
        LinearSys.aux_holdsOn Ar c G Lr d u0v wv Z (toReal Δt) k q := by
      intro q hq t ht1 ht2 b hb zs hzs
      set cb := LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (mulUp Y (acc q)) with hcb
      have hlt := toReal_lt_of_ltStrict hq
      rw [toReal_zero] at hlt
      have hadd1 := add_le_addUp (maximum (aff q) (aff' q)) cb
      have hadd2 := add_le_addUp (addUp (maximum (aff q) (aff' q)) cb) (inp q).2.2.1
      have hadd3 := add_le_addUp (addUp (addUp (maximum (aff q) (aff' q)) cb) (inp q).2.2.1)
        (cov' q)
      rw [toReal_maximum] at hadd1
      set τ := t - k * toReal Δt with hτ
      set lam := τ / toReal Δt with hlam
      have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hΔt.le
      have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hΔt]; linarith
      -- `λ ∈ [0, 1]` weighs the two ends; the curvature terms and the input cover the rest
      have hc := hcurv (Lr q ᵥ* Dr ^ k) (ℓ q) _ (hE0 q) τ (by linarith) (by linarith) b hb
      have hg := (hinp _ _ _ (hE0 q)).2.1 τ (by linarith) (by linarith)
      have hcv := hcov1 q zs hzs
      have ha0 := haff q b hb
      have ha1 := haff1 q b hb
      -- `∫₀^τ u₀ = λ w + (∫₀^τ − λ ∫₀^Δt) u₀`
      have hint : (Lr q ᵥ* Dr ^ k) ⬝ᵥ (Real.MatExp.expIntegral Ar τ *ᵥ u0v)
          = lam * ((Lr q ᵥ* Dr ^ k) ⬝ᵥ wv) + (Lr q ᵥ* Dr ^ k) ⬝ᵥ ((Real.MatExp.expIntegral Ar τ
            - lam • Real.MatExp.expIntegral Ar (toReal Δt)) *ᵥ u0v) := by
        rw [hwv, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
          smul_eq_mul]
        ring
      rw [LinearSys.aux_interp Ar (toReal Δt) k t (Lr q) (X b), hint]
      rw [hcwr q] at ha1
      have hlt' : max (toReal (aff q)) (toReal (aff' q)) + toReal cb
          + toReal (inp q).2.2.1 + toReal (cov' q) < 0 := by linarith
      exact LinearSys.aux_combine ha0 ha1 hc hg hcv hlt' hlam0 hlam1
    -- one step
    rw [LinearSys.step_verifySupportStepsFloat]
    dsimp only
    simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
    -- the flags so far and the new one
    have hflags' : ∀ flag : Fin r → Bool,
        (∀ q, flag q = true → LinearSys.aux_holdsOn Ar c G Lr d u0v wv Z (toReal Δt) k q) →
        ∀ i (hi : i < (flag :: flags).reverse.length) q, (flag :: flags).reverse[i] q = true →
          LinearSys.aux_holdsOn Ar c G Lr d u0v wv Z (toReal Δt) i q := by
      intro flag hf i hi q hq
      -- the reversed list is the old one and the new flag at index `k`
      have hr : (flag :: flags).reverse = flags.reverse ++ [flag] := List.reverse_cons
      have hi' : i < (flags.reverse ++ [flag]).length := hr ▸ hi
      have hget : (flag :: flags).reverse[i] = (flags.reverse ++ [flag])[i]'hi' := by
        simp only [hr]
      rw [hget, List.getElem_append] at hq
      split_ifs at hq with hik
      · exact hflags i hik q hq
      · have hik' : i = k := by simp at hik hi'; omega
        subst hik'
        simp at hq
        exact hf q hq
    have hrec := fun flag hf => ih (k := k + 1) (ℓ := ℓUp) (acc := acc') (aff := aff')
      (cw := cw') (cwd := cwd') (cov := cov') (cin := cin') (flags := flag :: flags)
      (hkN := by omega) (hlen := by simp [hlen])
      (hinv := ⟨hacc1, haff1, hcw1, hcwd1, hcov1, hcin1⟩) (hflags := hflags' flag hf)
    -- a falsifying row at `k + 1`, if within `T`; else the next step
    split
    · next q hfind =>
      have hlow := List.find?_some hfind
      split_ifs with hT
      · refine ⟨fun fl h => (by cases h), fun k' q' h => ?_⟩
        cases h
        have hΔq : (0 : ℝ) ≤ ((ToRat.toRat Δt : ℚ) : ℝ) := by
          rw [ToRat.toReal_toRat]; exact hΔt.le
        have hΔq' : (0 : ℚ) ≤ ToRat.toRat Δt := by exact_mod_cast hΔq
        refine ⟨by exact_mod_cast hT, mul_nonneg (Nat.cast_nonneg _) hΔq', ?_⟩
        have hpos := toReal_lt_of_ltStrict hlow
        rw [toReal_zero] at hpos
        -- a point of `X₀` and an input above the lower distance, which is above `d_q`
        obtain ⟨b, hb, hle⟩ := LinearSys.exists_le_dotProduct_verifySupportDownFloat c G hβX0 hβ
          (ℓUp q) (hE1 q)
        obtain ⟨zs, hzs, hzle⟩ := hcin1 q
        have hsub := subDown_le_sub (addDown (addDown (LinearSys.verifySupportDownFloat c G βX
          (ℓUp q) (mulUp Y (acc' q))) (cwd' q)) (cin' q)) (d q)
        have had1 := addDown_le_add (addDown (LinearSys.verifySupportDownFloat c G βX
          (ℓUp q) (mulUp Y (acc' q))) (cwd' q)) (cin' q)
        have had2 := addDown_le_add (LinearSys.verifySupportDownFloat c G βX
          (ℓUp q) (mulUp Y (acc' q))) (cwd' q)
        refine ⟨b, hb, zs, hzs, ?_⟩
        rw [show ((((k + 1 : ℕ)) : ℝ) * toReal Δt) = ((k + 1 : ℕ) : ℝ) * toReal Δt from rfl,
          LinearSys.aux_exp_pow, dotProduct_mulVec]
        linarith [hcwd1 q]
      · exact hrec _ hflag
    · exact hrec _ hflag


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
/-- The boxes of a pass enclose the input: the input solution's facts and `G u₀`. -/
private theorem LinearSys.aux_inputBoxes_mem (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 < toReal Δt) {u₀ : Interval (Mat 𝕋 n 1)}
    {MU : Interval (Mat 𝕋 n p)} {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n p}
    (hM : Mr ∈ MU.toSet) {I : LinearSys.VerifyInputSolution 𝕋 n p} {g : Interval (Mat 𝕋 n 1)}
    (hbox : LinearSys.step_verifySupportInputBoxesFloat sys.A s Δt u₀ MU = some
        (I, g)) : -- --- CONCL ---
    LinearSys.aux_inputFacts sys Δt I u0r Mr ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal Δt →
      (Real.MatExp.expIntegral (toRealMat sys.A) τ
        - (τ / toReal Δt) • Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt)) * u0r
        ∈ g.toSet := by -- --- PROOF ---
  unfold LinearSys.step_verifySupportInputBoxesFloat at hbox
  dsimp only at hbox
  split at hbox
  rotate_left
  · simp at hbox
  rename_i I' g' hI hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hbox
  obtain ⟨rfl, rfl⟩ := hbox
  -- without a constant input `u₀ = 0`, without any input also `M = 0`
  have hu0 : (!(List.finRange n).all fun l => (le (u₀.inf l 0) FloatOps.zero
      && le FloatOps.zero (u₀.inf l 0)) && (le (u₀.sup l 0) FloatOps.zero
      && le FloatOps.zero (u₀.sup l 0))) = false → u0r = 0 := by
    -- every entry's bracket is `[0, 0]`
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
  -- a zero test passed on `MU` makes `M` zero
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
  -- the input's solution: computed, or zero without an input
  constructor
  · split_ifs at hI with hhas
    · exact LinearSys.verifyInputSolutionFloat_mem sys hs hΔt hu hM I' (Option.mem_def.mpr hI)
    · -- no input: every box a point at zero
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hhas
      have hu' := hu0 hhas.1
      have hM' := hM0 hhas.2
      simp only [Option.some.injEq] at hI
      subst hI hu' hM'
      refine ⟨Interval.mem_mat_iff.mpr fun l c => ?_, fun i => i.elim0, fun i => i.elim0,
        Interval.mem_mat_iff.mpr fun l c => ?_, fun l => ?_, ?_⟩
      · simp [Interval.point, toReal_zero]
      · simp [Interval.point, toReal_zero]
      · simp [toReal_zero]
      intro z hz
      obtain ⟨b, -, y, hy, hzeq⟩ :=
        sys.exists_eq_taylor_add_of_mem_inputReach (0 : Mat ℝ n p) hΔt 0 hz
      refine ⟨fun i => i.elim0, fun i => i.elim0, y, fun l => ?_, ?_⟩
      · have h := hy l
        simp only [Matrix.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero] at h
        simp only [toReal_zero]; exact h
      · rw [hzeq]; simp
  -- `G u₀`: the correction matrix times the box of `u₀`, or zero
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
/-- A fold of `addUp` from `a` is at least `a` plus the exact sum. -/
private theorem LinearSys.aux_le_foldl {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun X => toReal (f X)).sum
        ≤ toReal (L.foldl (fun acc X => addUp acc (f X)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons X L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have h := ih (addUp a (f X))
    linarith [add_le_addUp a (f X)]

omit [ToRat 𝕋] in
/-- `max 0 (maxₗ divUp (x l) (s l))` bounds every `x l / s l`. -/
private theorem LinearSys.aux_beta {s x : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) (l
    : Fin n) : -- --- CONCL ---
    toReal (x l) ≤ toReal (maximum FloatOps.zero (maximumOver fun l => divUp (x l) (s l)))
      * toReal (s l) := by -- --- PROOF ---
  have hdiv := div_le_divUp (x l) (s l) (hs l)
  rw [div_le_iff₀ (hs l)] at hdiv
  have hmax : toReal (divUp (x l) (s l))
      ≤ toReal (maximum FloatOps.zero (maximumOver fun l => divUp (x l) (s l))) := by
    rw [toReal_maximum]
    exact le_trans (le_maximumOver (fun l => divUp (x l) (s l)) l) (le_max_right _ _)
  exact le_trans hdiv (mul_le_mul_of_nonneg_right hmax (hs l).le)

omit [ToRat 𝕋] in
/-- And it is nonnegative. -/
private theorem LinearSys.aux_beta0 (x : Fin n → 𝕋) :
    0 ≤ toReal (maximum FloatOps.zero (maximumOver x)) := by
  rw [toReal_maximum, toReal_zero]; exact le_max_left _ _

omit [ToRat 𝕋] in
/-- The input's terms of a pass bound what they claim (`LinearSys.aux_inputBound`). -/
private theorem LinearSys.aux_inputBoxes_bound (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 < toReal Δt) {u₀ : Interval (Mat 𝕋 n 1)}
    {MU : Interval (Mat 𝕋 n p)} {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n p}
    (hM : Mr ∈ MU.toSet) {I : LinearSys.VerifyInputSolution 𝕋 n p} {g : Interval (Mat 𝕋 n 1)}
    (hbox : LinearSys.step_verifySupportInputBoxesFloat sys.A s Δt u₀ MU = some
        (I, g)) : -- --- CONCL ---
    LinearSys.aux_inputBound s I g
      (maximum FloatOps.zero (maximumOver fun l =>
        divUp (sumUp fun c => I.w.magnitudeMat l c) (s l)))
      (maximum FloatOps.zero (maximumOver fun l =>
        divUp (sumUp fun c => g.magnitudeMat l c) (s l)))
      (maximum FloatOps.zero (maximumOver fun l => divUp (addUp (I.V.foldl (fun acc X =>
        addUp acc (sumUp fun c => X.magnitudeMat l c)) FloatOps.zero) (I.ρ l)) (s l)))
      (fun l => u0r l 0)
      (Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) *ᵥ fun l => u0r l 0)
      (sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (toReal Δt))
      (toRealMat sys.A) (toReal Δt) := by -- --- PROOF ---
  obtain ⟨⟨hw, X, hX, hXs, hR, hdec⟩, hg⟩ := LinearSys.aux_inputBoxes_mem sys hs hΔt hu hM hbox
  set A := toRealMat sys.A
  -- a column vector's entries are its only column's
  have hcol : ∀ Q : Mat ℝ n n, (fun l => ∑ c : Fin 1, (Q * u0r) l c) = Q *ᵥ fun l => u0r l 0 := by
    intro Q; funext l; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  -- the bounds of the magnitudes' scaled row sums
  have hmagsum : ∀ {k' : ℕ} (Xb : Interval (Mat 𝕋 n k')) (l : Fin n),
      ∑ c, toReal (Xb.magnitudeMat l c) ≤ toReal (sumUp fun c => Xb.magnitudeMat l c) :=
    fun Xb l => sum_le_sumUp _
  have hβw := fun l => LinearSys.aux_beta (x := fun l => sumUp fun c => I.w.magnitudeMat l c) hs l
  have hβg := fun l => LinearSys.aux_beta (x := fun l => sumUp fun c => g.magnitudeMat l c) hs l
  let fU : Fin n → 𝕋 := fun l =>
    I.V.foldl (fun acc X => addUp acc (sumUp fun c => X.magnitudeMat l c)) FloatOps.zero
  let xU : Fin n → 𝕋 := fun l => addUp (fU l) (I.ρ l)
  have hβU := fun l => LinearSys.aux_beta (x := xU) hs l
  -- `Σᵢ Σ_c |Vᵢ| + ρ ≤ βU s`
  have hVsum : ∀ l, (I.V.map fun X => ∑ c, toReal (X.magnitudeMat l c)).sum + toReal (I.ρ l)
      ≤ toReal (maximum FloatOps.zero (maximumOver fun l => divUp (xU l) (s l)))
        * toReal (s l) := by
    intro l
    refine le_trans ?_ (hβU l)
    have hf := LinearSys.aux_le_foldl (fun X : Interval (Mat 𝕋 n p) =>
      sumUp fun c => X.magnitudeMat l c) I.V FloatOps.zero
    rw [toReal_zero, zero_add] at hf
    have hm : (I.V.map fun X => ∑ c, toReal (X.magnitudeMat l c)).sum
        ≤ (I.V.map fun X => toReal (sumUp fun c => X.magnitudeMat l c)).sum :=
      List.sum_le_sum fun X _ => sum_le_sumUp _
    linarith [add_le_addUp (fU l) (I.ρ l)]
  intro ℓr ℓ E hE
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `ℓ' w` from above
    have h := LinearSys.dotProduct_le_verifyBoxDotUpFloat hw (LinearSys.aux_beta0 _)
      (fun l => le_trans (hmagsum _ l) (hβw l)) ℓ hE
    rwa [hcol] at h
  · -- and from below
    have h := LinearSys.verifyBoxDotDownFloat_le_dotProduct hw (LinearSys.aux_beta0 _)
      (fun l => le_trans (hmagsum _ l) (hβw l)) ℓ hE
    rwa [hcol] at h
  · -- `ℓ' G u₀`
    intro τ hτ0 hτ1
    have h := LinearSys.dotProduct_le_verifyBoxDotUpFloat (hg τ hτ0 hτ1) (LinearSys.aux_beta0 _)
      (fun l => le_trans (hmagsum _ l) (hβg l)) ℓ hE
    rwa [hcol] at h
  · -- the varying input, from above
    intro z hz
    obtain ⟨b, hb, y, hy, rfl⟩ := hdec z hz
    exact LinearSys.dotProduct_le_verifyInputOuterFloat (LinearSys.aux_beta0 _) hVsum ℓ hE hX hb hy
  · -- held at the sign of `ℓ' PG`, from below
    set PG := Real.MatExp.expIntegral A (toReal Δt) * Mr with hPG
    set β : Fin p → ℝ := fun c => if 0 ≤ ℓr ⬝ᵥ (fun l => PG l c) then 1 else -1 with hβdef
    have hβmem : β ∈ Set.Icc (-1 : Fin p → ℝ) 1 := ⟨fun c => by
      simp only [hβdef, Pi.neg_apply, Pi.one_apply]; split_ifs <;> norm_num, fun c => by
      simp only [hβdef, Pi.one_apply]; split_ifs <;> norm_num⟩
    refine ⟨Real.MatExp.expIntegral A (toReal Δt) *ᵥ (Mr *ᵥ β),
      sys.expIntegral_mem_inputReach hΔt.le ⟨β, hβmem, rfl⟩, ?_⟩
    have hval : ℓr ⬝ᵥ (Real.MatExp.expIntegral A (toReal Δt) *ᵥ (Mr *ᵥ β))
        = ∑ c, |ℓr ⬝ᵥ (fun l => PG l c)| := by
      rw [Matrix.mulVec_mulVec, ← hPG, dotProduct_mulVec]
      refine Finset.sum_congr rfl fun c _ => ?_
      show (∑ l, ℓr l * PG l c) * β c = _
      simp only [hβdef]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]; rfl
      · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]; rfl
    rw [hval]
    -- `Σ_c |PG_lc| ≤ Σᵢ Σ_c |Vᵢ| + ρ_l`
    have hPGβ : ∀ l, ∑ c, |PG l c|
        ≤ toReal (maximum FloatOps.zero (maximumOver fun l => divUp (xU l) (s l))) * toReal (s l)
        := by
      intro l
      refine le_trans ?_ (hVsum l)
      have hx : ∑ c, |(∑ i, X i) l c|
          ≤ (I.V.map fun X => ∑ c, toReal (X.magnitudeMat l c)).sum := by
        -- each order within its box's magnitude
        rw [← Fin.sum_univ_fun_getElem]
        simp only [Matrix.sum_apply]
        refine le_trans (Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _) ?_
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ => ?_
        have hmem := Interval.mem_mat_iff.mp (hX i) l c
        rw [Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
        exact abs_le_max_abs_abs hmem.1 hmem.2
      -- the orders' sum plus the remainder bound the exact matrix
      have htri : ∑ c, |PG l c| ≤ ∑ c, |(∑ i, X i) l c| + ∑ c, |PG l c - (∑ i, X i) l c| := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun c _ => ?_
        have := abs_add_le ((∑ i, X i) l c) (PG l c - (∑ i, X i) l c)
        rwa [add_sub_cancel] at this
      linarith [hR l]
    exact LinearSys.verifyInputInnerFloat_le (LinearSys.aux_beta0 _) hPGβ ℓ hE hXs hR


omit [ToRat 𝕋] in
/-- The curvature term of a pass from its correction matrix `F`. -/
private theorem LinearSys.aux_curvBound_of (sys : LinearSys 𝕋 n) {s c : Vec 𝕋 n} {G : Mat 𝕋 n m}
    {v : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i))
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i)) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {P₀ : ℕ} {F : Interval (Mat 𝕋 n n)}
    (hcor : MatExp.verifyCorrectionStateFloat sys.A s Δt = some (P₀, F)) : -- --- CONCL ---
    let Fc : Mat 𝕋 n n := fun j k => addUp (F.inf j k) (half (subUp (F.sup j k) (F.inf j k)))
    let Fr : Mat 𝕋 n n := fun j k => maximum (subUp (F.sup j k) (Fc j k))
      (subUp (Fc j k) (F.inf j k))
    let Fm : Mat 𝕋 n n := fun j k => addUp (absolute (Fc j k)) (Fr j k)
    LinearSys.aux_curvBound s c G (⟨mulVecDown Fc c, mulVecUp Fc c⟩ : Interval _)
      (⟨matMulDown Fc G, matMulUp Fc G⟩ : Interval _) (mulVecUp Fr v)
      (maximum FloatOps.zero (maximumOver fun i => divUp (mulVecUp Fm v i) (s i)))
      (toRealMat sys.A) (toReal Δt) := by -- --- PROOF ---
  intro Fc Fr Fm
  have hv0 : ∀ i, 0 ≤ toReal (v i) := fun i =>
    le_trans (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (hv i)
  intro ℓr ℓ E hE τ hτ0 hτ1 b hb
  have hmem := MatExp.expDiff_mem_verifyCorrectionStateFloat sys.A hs hΔt (P₀, F)
    (Option.mem_def.mpr hcor) τ hτ0 hτ1
  have hFσ := Interval.mem_mat_iff.mp hmem
  refine LinearSys.dotProduct_le_verifyCurvatureUpFloat (Fc := Fc) (Fr := Fr)
    (wc := ⟨mulVecDown Fc c, mulVecUp Fc c⟩) (WG := ⟨matMulDown Fc G, matMulUp Fc G⟩) c G
    (fun i => by exact ⟨dotDown_le (Fc i) c, le_dotUp (Fc i) c⟩)
    (Interval.mem_mat_iff.mpr fun i j => by
      exact ⟨dotDown_le (Fc i) fun l => G l j, le_dotUp (Fc i) fun l => G l j⟩) hv
    (fun i => le_dotUp (Fr i) v) ?_ ?_ ℓ hE (fun i k => ?_) hb
  · rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  -- `βF` bounds every `Σₖ |F|ᵢₖ vₖ / sᵢ`
  · intro i
    have hsum : ∑ k, (|toReal (Fc i k)| + toReal (Fr i k)) * toReal (v k)
        ≤ toReal (mulVecUp Fm v i) := by
      refine le_trans (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (hv0 k))
        (le_dotUp (Fm i) v)
      have := add_le_addUp (absolute (Fc i k)) (Fr i k)
      rwa [toReal_absolute] at this
    have hdiv := div_le_divUp (mulVecUp Fm v i) (s i) (hs i)
    have hmax : toReal (divUp (mulVecUp Fm v i) (s i))
        ≤ toReal (maximum FloatOps.zero
          (maximumOver fun i => divUp (mulVecUp Fm v i) (s i))) := by
      rw [toReal_maximum]
      exact le_trans (le_maximumOver (fun i => divUp (mulVecUp Fm v i) (s i)) i)
        (le_max_right _ _)
    rw [div_le_iff₀ (hs i)] at hdiv
    exact le_trans hsum (le_trans hdiv (mul_le_mul_of_nonneg_right hmax (hs i).le))
  -- `F_σ` is within `F_r` of `F_c`
  · obtain ⟨hlo, hhi⟩ := hFσ i k
    have h1 := sub_le_subUp (F.sup i k) (Fc i k)
    have h2 := sub_le_subUp (Fc i k) (F.inf i k)
    show |_ - toReal (Fc i k)| ≤ toReal (maximum (subUp (F.sup i k) (Fc i k))
      (subUp (Fc i k) (F.inf i k)))
    rw [toReal_maximum, abs_le]
    constructor
    · linarith [le_max_right (toReal (subUp (F.sup i k) (Fc i k)))
        (toReal (subUp (Fc i k) (F.inf i k)))]
    · linarith [le_max_left (toReal (subUp (F.sup i k) (Fc i k)))
        (toReal (subUp (Fc i k) (F.inf i k)))]


-- =======================================  MAIN THEOREM  ======================================= --

set_option maxHeartbeats 400000 in -- the pass is unfolded whole, with every `let` of its body
theorem LinearSys.verifySupportPassFloat_sound (sys : LinearSys 𝕋 n) {s c : Vec 𝕋 n}
    {G : Mat 𝕋 n m} {v : Vec 𝕋 n} {βX κ μ : 𝕋} {u₀ : Interval (Mat 𝕋 n 1)}
    {MU : Interval (Mat 𝕋 n p)} {ℓ₀ : Mat 𝕋 r n} {E₀ d : Vec 𝕋 r} {Δt : 𝕋} {N : ℕ} {T : ℚ}
    {Lr : Fin r → Vec ℝ n} {u0r : Mat ℝ n 1} {Mr : Mat ℝ n p} (hs : ∀ i, 0 < toReal (s i))
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i)) (hβX0 : 0 ≤ toReal βX)
    (hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i))
    (hμ : ∀ t : ℝ, 0 ≤ t → ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat sys.A))‖ ≤
      toReal κ * Real.exp (t * toReal μ))
    (hE₀ : ∀ q, ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (E₀ q))
    (hu : u0r ∈ u₀.toSet) (hM : Mr ∈ MU.toSet) : -- --- CONCL ---
    let Z := sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (toReal Δt)
    let u0v : Vec ℝ n := fun l => u0r l 0
    let wv := Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) *ᵥ u0v
    let ℓ := fun q (j : ℕ) => Lr q ᵥ* exp (toReal Δt • toRealMat sys.A) ^ j
    (∀ fl, LinearSys.verifySupportPassFloat sys.A s c G v βX κ μ u₀ MU ℓ₀ E₀ d Δt N T
        = .decided fl → 0 < toReal Δt ∧ fl.length = N ∧ ∀ i (hi : i < fl.length) q,
        fl[i] q = true → ∀ t : ℝ, i * toReal Δt ≤ t → t ≤ (i + 1) * toReal Δt → ∀ b : Fin m → ℝ,
        (∀ j, |b j| ≤ 1) → ∀ zs : ℕ → Vec ℝ n, (∀ j < i + 1, zs j ∈ Z) →
        Lr q ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b))
          + ℓ q i ⬝ᵥ (Real.MatExp.expIntegral (toRealMat sys.A) (t - i * toReal Δt) *ᵥ u0v)
          + ∑ j ∈ Finset.range i, ℓ q j ⬝ᵥ wv + ∑ j ∈ Finset.range (i + 1), ℓ q j ⬝ᵥ zs j
          < toReal (d q))
    ∧ (∀ k q, LinearSys.verifySupportPassFloat sys.A s c G v βX κ μ u₀ MU ℓ₀ E₀ d Δt N T
        = .falsified k q → 0 < toReal Δt ∧
      (k : ℚ) * ToRat.toRat Δt ≤ T ∧ 0 ≤ (k : ℚ) * ToRat.toRat Δt ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ ∃ zs : ℕ → Vec ℝ n, (∀ j < k, zs j ∈ Z) ∧
        toReal (d q) < Lr q ⬝ᵥ (exp (((k : ℝ) * toReal Δt) • toRealMat sys.A) *ᵥ
          (toRealVec c + toRealMat G *ᵥ b))
          + ∑ j ∈ Finset.range k, ℓ q j ⬝ᵥ wv + ∑ j ∈ Finset.range k, ℓ q j ⬝ᵥ zs j)
    := by -- --- PROOF ---
  intro Z u0v wv ℓ
  have hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i) :=
    fun i => le_trans (hv i) (hβX i)
  have hv0 : ∀ i, 0 ≤ toReal (v i) := fun i =>
    le_trans (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (hv i)
  have hE0 : ∀ q, 0 ≤ toReal (E₀ q) := fun q =>
    le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hs i).le) (hE₀ q)
  -- the correction matrix, the exponential and the input's boxes, or no outcome to check
  unfold LinearSys.verifySupportPassFloat
  rcases hcor : MatExp.verifyCorrectionStateFloat sys.A s Δt with _ | ⟨P₀, F⟩
  · simp
  -- the exponential's ball and the input's boxes, or no pass
  rcases hball : MatExp.expBallFloat sys.A s Δt with _ | ⟨D, rD⟩
  · simp
  rcases hbox : LinearSys.step_verifySupportInputBoxesFloat sys.A s Δt u₀ MU with _ | ⟨I, g⟩
  · simp
  dsimp only
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
  split_ifs with hif
  swap
  · simp
  -- a positive step and a growth bound that does not overflow
  obtain ⟨hpos, hle⟩ := Bool.and_eq_true _ _ ▸ hif
  have hΔt := toReal_lt_of_ltStrict hpos
  rw [toReal_zero] at hΔt
  obtain ⟨hY1, hY⟩ := LinearSys.aux_growth sys.A hΔt hμ rfl hle
  set Y := maximum FloatOps.one
    (mulUp κ (expUp 30 (mulUp (maximum μ FloatOps.zero) (mulUp (nsmulUp N FloatOps.one) Δt))))
  have hD := MatExp.norm_scaleConj_exp_sub_le_expBallFloat sys.A hs hΔt.le (D, rD)
    (Option.mem_def.mpr hball)
  have hcurv := LinearSys.aux_curvBound_of sys hs hv hΔt hcor
  -- the input
  have hinp := LinearSys.aux_inputBoxes_bound sys hs hΔt hu hM hbox
  -- the steps from `ℓ₀`, with the initial errors and distances
  have hY0 : 0 ≤ toReal Y := by linarith
  have h := LinearSys.aux_steps (Ar := toRealMat sys.A) (Lr := Lr) (T := T) (d := d) hs hβX0 hΔt
      hY0 hβ hY hD hcurv hinp rfl
    N 0 ℓ₀ E₀ (fun q => subUp (addUp (LinearSys.verifySupportUpFloat c G βX (ℓ₀ q)
      (mulUp Y (E₀ q))) FloatOps.zero) (d q)) (fun _ => FloatOps.zero) (fun _ => FloatOps.zero)
    (fun _ => FloatOps.zero) (fun _ => FloatOps.zero) [] (by omega) rfl
    ⟨?_, ?_, fun q => by simp [toReal_zero], fun q => by simp [toReal_zero],
      fun q zs _ => by simp [toReal_zero],
      fun q => ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j), by simp [toReal_zero]⟩⟩
    (fun i hi => by simp at hi)
  · exact ⟨fun fl hfl => ⟨hΔt, (h.1 fl hfl).1, fun i hi q hq => (h.1 fl hfl).2 i hi q hq⟩,
      fun k' q' hf => ⟨hΔt, h.2 k' q' hf⟩⟩
  · -- the errors of the rows carried
    intro q p hp
    rw [pow_zero, Matrix.vecMul_one]
    have h := Real.MatExp.weightedSum_vecMul_le hs (Lr q - toRealVec (ℓ₀ q))
      (exp (toReal Δt • toRealMat sys.A) ^ p)
    refine le_trans h ?_
    rw [mul_comm (toReal Y)]
    exact mul_le_mul (hE₀ q) (hY p (by omega)) (norm_nonneg _) (hE0 q)
  · -- the distances at `t_0`
    intro q b hb
    rw [pow_zero, Matrix.vecMul_one, Finset.range_zero, Finset.sum_empty, add_zero]
    have hE : ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (mulUp Y (E₀ q)) := by
      refine le_trans (hE₀ q) (le_trans ?_ (mul_le_mulUp _ _))
      nlinarith [hE0 q]
    have h := LinearSys.dotProduct_le_verifySupportUpFloat c G hβX0 hβ (ℓ₀ q) hE hb
    have h2 := add_le_addUp (LinearSys.verifySupportUpFloat c G βX (ℓ₀ q) (mulUp Y (E₀ q)))
      FloatOps.zero
    rw [toReal_zero, add_zero] at h2
    exact le_trans (by linarith) (sub_le_subUp _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
