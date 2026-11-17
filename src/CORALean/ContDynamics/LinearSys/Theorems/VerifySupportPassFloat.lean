module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportPassFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrectionStateFloat
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
* `hμ` – `‖S⁻¹ e^{tA} S‖ ≤ e^{tμ}` for `t ≥ 0`
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m r : ℕ}


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
/-- `Y = e↑(a)` is at least `1` and bounds the weighted norm of `D^p` for every `p ≤ N`. -/
private theorem LinearSys.aux_growth (A : Mat 𝕋 n n) {s : Vec 𝕋 n} {μ Δt a : 𝕋} {N : ℕ}
    (hΔt : 0 < toReal Δt)
    (hμ : ∀ t : ℝ, 0 ≤ t →
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤ Real.exp (t * toReal μ))
    (hadef : a = mulUp (maximum μ FloatOps.zero) (mulUp (nsmulUp N FloatOps.one) Δt))
    (ha : le a (Nat.iterate (fun x => addDown x x) 29 FloatOps.one) = true) : -- --- CONCL ---
    1 ≤ toReal (expUp 30 a) ∧ ∀ p ≤ N,
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • toRealMat A) ^ p)‖
        ≤ toReal (expUp 30 a) := by -- --- PROOF ---
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
  have ha0 : 0 ≤ toReal a := le_trans (mul_nonneg hμ0 (by positivity)) ha'
  refine ⟨le_trans (Real.one_le_exp ha0) hexp, fun p hp => ?_⟩
  rw [← LinearSys.aux_exp_pow]
  refine le_trans (hμ _ (by positivity)) (le_trans (Real.exp_le_exp.mpr ?_) hexp)
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


/-- Row `q` holds over step `i` of length `h` for every point of `X₀`. -/
private def LinearSys.aux_holdsOn (Ar : Mat ℝ n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Lr : Fin r → Vec ℝ n) (d : Vec 𝕋 r) (h : ℝ) (i : ℕ) (q : Fin r) : Prop :=
  ∀ t : ℝ, i * h ≤ t → t ≤ (i + 1) * h → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
    Lr q ⬝ᵥ (exp (t • Ar) *ᵥ (toRealVec c + toRealMat G *ᵥ b)) < toReal (d q)

/-- The curvature term bounds `ℓ (e^{τA} − I − (τ/Δt)(D − I)) x` over a step, for every direction
within its error. -/
private def LinearSys.aux_curvBound (s c : Vec 𝕋 n) (G : Mat 𝕋 n m) (wc : Interval (Vec 𝕋 n))
    (WG : Interval (Mat 𝕋 n m)) (wr : Vec 𝕋 n) (βF : 𝕋) (Ar : Mat ℝ n n) (h : ℝ) : Prop :=
  ∀ (ℓr : Vec ℝ n) (ℓ : Vec 𝕋 n) (E : 𝕋),
    ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E → ∀ τ : ℝ, 0 ≤ τ → τ ≤ h →
    ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
    ℓr ⬝ᵥ ((exp (τ • Ar) - 1 - (τ / h) • (exp (h • Ar) - 1)) *ᵥ (toRealVec c + toRealMat G *ᵥ b))
      ≤ toReal (LinearSys.verifyCurvatureUpFloat wc WG wr βF ℓ E)

/-- The steps keep the invariant: the carried errors, the distances, the flags so far. -/
private theorem LinearSys.aux_steps {s c : Vec 𝕋 n} {G : Mat 𝕋 n m} {βX : 𝕋}
    {wc : Interval (Vec 𝕋 n)} {WG : Interval (Mat 𝕋 n m)} {wr : Vec 𝕋 n} {βF : 𝕋}
    {D : Mat 𝕋 n n} {rD Y : 𝕋} {d : Vec 𝕋 r} {Δt : 𝕋} {T : ℚ} {Ar : Mat ℝ n n}
    {Lr : Fin r → Vec ℝ n} {N : ℕ} (hs : ∀ i, 0 < toReal (s i)) (hβX0 : 0 ≤ toReal βX)
    (hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i))
    (hΔt : 0 < toReal Δt) (hY0 : 0 ≤ toReal Y)
    (hY : ∀ p ≤ N, ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • Ar) ^ p)‖ ≤ toReal Y)
    (hD : ‖Real.MatExp.scaleConj (toRealVec s) (exp (toReal Δt • Ar) - toRealMat D)‖ ≤ toReal rD)
    (hcurv : LinearSys.aux_curvBound s c G wc WG wr βF Ar (toReal Δt))
    (fuel k : ℕ) (ℓ : Mat 𝕋 r n) (acc aff : Vec 𝕋 r) (flags : List (Fin r → Bool))
    (hkN : k + fuel = N)
    (hacc : ∀ q p, k + p ≤ N →
      ∑ i, |((Lr q ᵥ* exp (toReal Δt • Ar) ^ k - toRealVec (ℓ q)) ᵥ* exp (toReal Δt • Ar) ^ p) i|
        * toReal (s i) ≤ toReal Y * toReal (acc q))
    (haff : ∀ q (b : Fin m → ℝ), (∀ j, |b j| ≤ 1) →
      (Lr q ᵥ* exp (toReal Δt • Ar) ^ k) ⬝ᵥ (toRealVec c + toRealMat G *ᵥ b) - toReal (d q)
        ≤ toReal (aff q))
    (hlen : flags.length = k)
    (hflags : ∀ i (hi : i < flags.reverse.length) q, flags.reverse[i] q = true →
      LinearSys.aux_holdsOn Ar c G Lr d (toReal Δt) i q) : -- --- CONCL ---
    (∀ fl, LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF D rD Y d Δt T k fuel ℓ
        acc aff flags = .decided fl → fl.length = N ∧
      ∀ i (hi : i < fl.length) q, fl[i] q = true →
        LinearSys.aux_holdsOn Ar c G Lr d (toReal Δt) i q)
    ∧ (∀ k' q, LinearSys.step_verifySupportStepsFloat s c G βX wc WG wr βF D rD Y d Δt T k fuel ℓ
        acc aff flags = .falsified k' q → (k' : ℚ) * ToRat.toRat Δt ≤ T ∧
      0 ≤ (k' : ℚ) * ToRat.toRat Δt ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ toReal (d q)
        < Lr q ⬝ᵥ (exp (((k' : ℝ) * toReal Δt) • Ar) *ᵥ
          (toRealVec c + toRealMat G *ᵥ b))) := by -- --- PROOF ---
  set Dr := exp (toReal Δt • Ar)
  set X := fun b : Fin m → ℝ => toRealVec c + toRealMat G *ᵥ b
  induction fuel generalizing k ℓ acc aff flags with
  | zero =>
    simp only [LinearSys.step_verifySupportStepsFloat, reduceCtorEq, false_imp_iff,
      implies_true, and_true]
    rintro fl ⟨⟩
    exact ⟨by rw [List.length_reverse]; omega, hflags⟩
  | succ fuel ih =>
    -- the new rows, errors and distances
    set ℓUp : Mat 𝕋 r n := fun q j => dotUp (ℓ q) fun i => D i j with hℓUp
    set δ : Vec 𝕋 r := fun q => addUp (mulUp (sumUp fun j => mulUp (absolute (ℓ q j)) (s j)) rD)
      (sumUp fun j => mulUp (subUp (ℓUp q j) (dotDown (ℓ q) fun i => D i j)) (s j)) with hδ
    set acc' : Vec 𝕋 r := fun q => addUp (acc q) (δ q) with hacc'
    set aff' : Vec 𝕋 r := fun q => subUp (LinearSys.verifySupportUpFloat c G βX (ℓUp q)
      (mulUp Y (acc' q))) (d q) with haff'
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
    -- the error of the new rows
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
    -- the distances at `k + 1`
    have haff1 : ∀ q (b : Fin m → ℝ), (∀ j, |b j| ≤ 1) →
        (Lr q ᵥ* Dr ^ (k + 1)) ⬝ᵥ X b - toReal (d q) ≤ toReal (aff' q) := by
      intro q b hb
      have h := LinearSys.dotProduct_le_verifySupportUpFloat c G hβX0 hβ (ℓUp q) (hE1 q) hb
      exact le_trans (by linarith) (sub_le_subUp _ _)
    -- a set flag holds over the step
    have hflag : ∀ q, ltStrict (addUp (maximum (aff q) (aff' q))
        (LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (mulUp Y (acc q)))) zero = true →
        ∀ t : ℝ, k * toReal Δt ≤ t → t ≤ (k + 1) * toReal Δt → ∀ b : Fin m → ℝ,
          (∀ j, |b j| ≤ 1) → Lr q ⬝ᵥ (exp (t • Ar) *ᵥ X b) < toReal (d q) := by
      intro q hq t ht1 ht2 b hb
      have hlt := toReal_lt_of_ltStrict hq
      rw [toReal_zero] at hlt
      have hadd := add_le_addUp (maximum (aff q) (aff' q))
        (LinearSys.verifyCurvatureUpFloat wc WG wr βF (ℓ q) (mulUp Y (acc q)))
      rw [toReal_maximum] at hadd
      have hlam0 : 0 ≤ (t - k * toReal Δt) / toReal Δt := div_nonneg (by linarith) hΔt.le
      have hlam1 : (t - k * toReal Δt) / toReal Δt ≤ 1 := by
        rw [div_le_one hΔt]; linarith
      -- `λ ∈ [0, 1]` weighs the two ends; the curvature term covers the rest
      have hc := hcurv (Lr q ᵥ* Dr ^ k) (ℓ q) _ (hE0 q) (t - k * toReal Δt) (by linarith)
        (by linarith) b hb
      have ha0 := haff q b hb
      have ha1 := haff1 q b hb
      rw [LinearSys.aux_interp Ar (toReal Δt) k t (Lr q) (X b)]
      have hmax0 := le_max_left (toReal (aff q)) (toReal (aff' q))
      have hmax1 := le_max_right (toReal (aff q)) (toReal (aff' q))
      nlinarith
    -- one step
    rw [LinearSys.step_verifySupportStepsFloat]
    dsimp only
    simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
    -- the flags so far and the new one
    have hflags' : ∀ flag : Fin r → Bool,
        (∀ q, flag q = true → LinearSys.aux_holdsOn Ar c G Lr d (toReal Δt) k q) →
        ∀ i (hi : i < (flag :: flags).reverse.length) q, (flag :: flags).reverse[i] q = true →
          LinearSys.aux_holdsOn Ar c G Lr d (toReal Δt) i q := by
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
      (flags := flag :: flags) (hkN := by omega) (hacc := hacc1) (haff := haff1)
      (hlen := by simp [hlen]) (hflags := hflags' flag hf)
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
        -- a point of `X₀` above the lower distance, which is above `d_q`
        obtain ⟨b, hb, hle⟩ := LinearSys.exists_le_dotProduct_verifySupportDownFloat c G hβX0 hβ
          (ℓUp q) (hE1 q)
        have hsub := subDown_le_sub (LinearSys.verifySupportDownFloat c G βX (ℓUp q)
          (mulUp Y (acc' q))) (d q)
        refine ⟨b, hb, ?_⟩
        rw [show ((((k + 1 : ℕ)) : ℝ) * toReal Δt) = ((k + 1 : ℕ) : ℝ) * toReal Δt from rfl,
          LinearSys.aux_exp_pow, dotProduct_mulVec]
        linarith
      · exact hrec _ hflag
    · exact hrec _ hflag


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySupportPassFloat_sound (A : Mat 𝕋 n n) {s c : Vec 𝕋 n} {G : Mat 𝕋 n m}
    {v : Vec 𝕋 n} {βX μ : 𝕋} {ℓ₀ : Mat 𝕋 r n} {E₀ d : Vec 𝕋 r} {Δt : 𝕋} {N : ℕ} {T : ℚ}
    {Lr : Fin r → Vec ℝ n} (hs : ∀ i, 0 < toReal (s i))
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i)) (hβX0 : 0 ≤ toReal βX)
    (hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i))
    (hμ : ∀ t : ℝ, 0 ≤ t →
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤ Real.exp (t * toReal μ))
    (hE₀ : ∀ q, ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (E₀ q)) : -- --- CONCL ---
    (∀ fl, LinearSys.verifySupportPassFloat A s c G v βX μ ℓ₀ E₀ d Δt N T = .decided fl →
      fl.length = N ∧ ∀ i (hi : i < fl.length) q, fl[i] q = true → ∀ t : ℝ,
        i * toReal Δt ≤ t → t ≤ (i + 1) * toReal Δt → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
        Lr q ⬝ᵥ (exp (t • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)) < toReal (d q))
    ∧ (∀ k q, LinearSys.verifySupportPassFloat A s c G v βX μ ℓ₀ E₀ d Δt N T = .falsified k q →
      (k : ℚ) * ToRat.toRat Δt ≤ T ∧ 0 ≤ (k : ℚ) * ToRat.toRat Δt ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ toReal (d q)
        < Lr q ⬝ᵥ (exp (((k : ℝ) * toReal Δt) • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)))
    := by -- --- PROOF ---
  have hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i) :=
    fun i => le_trans (hv i) (hβX i)
  have hv0 : ∀ i, 0 ≤ toReal (v i) := fun i =>
    le_trans (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (hv i)
  have hE0 : ∀ q, 0 ≤ toReal (E₀ q) := fun q =>
    le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hs i).le) (hE₀ q)
  -- the correction matrix and the exponential, or no outcome to check
  unfold LinearSys.verifySupportPassFloat
  rcases hcor : MatExp.verifyCorrectionStateFloat A s Δt with _ | ⟨P₀, F⟩
  · simp
  rcases hball : MatExp.expBallFloat A s Δt with _ | ⟨D, rD⟩
  · simp
  dsimp only
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
  split_ifs with hif
  swap
  · simp
  obtain ⟨hpos, hle⟩ := Bool.and_eq_true _ _ ▸ hif
  have hΔt := toReal_lt_of_ltStrict hpos
  rw [toReal_zero] at hΔt
  obtain ⟨hY1, hY⟩ := LinearSys.aux_growth A hΔt hμ rfl hle
  set Y := expUp 30 (mulUp (maximum μ FloatOps.zero) (mulUp (nsmulUp N FloatOps.one) Δt))
  -- `F`'s center, radius and magnitude bound, as the definition names them
  set Fc : Mat 𝕋 n n := fun j k => addUp (F.inf j k) (half (subUp (F.sup j k) (F.inf j k)))
    with hFc
  set Fr : Mat 𝕋 n n := fun j k => maximum (subUp (F.sup j k) (Fc j k))
    (subUp (Fc j k) (F.inf j k)) with hFr
  set Fm : Mat 𝕋 n n := fun j k => addUp (absolute (Fc j k)) (Fr j k) with hFm
  have hD := MatExp.norm_scaleConj_exp_sub_le_expBallFloat A hs hΔt.le (D, rD)
    (Option.mem_def.mpr hball)
  -- the curvature term
  have hcurv : LinearSys.aux_curvBound s c G (⟨mulVecDown Fc c, mulVecUp Fc c⟩ : Interval _)
      (⟨matMulDown Fc G, matMulUp Fc G⟩ : Interval _) (mulVecUp Fr v)
      (maximum FloatOps.zero (maximumOver fun i => divUp (mulVecUp Fm v i) (s i)))
      (toRealMat A) (toReal Δt) := by
    intro ℓr ℓ E hE τ hτ0 hτ1 b hb
    have hmem := MatExp.expDiff_mem_verifyCorrectionStateFloat A hs hΔt (P₀, F)
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
  -- the steps from `ℓ₀`, with the initial errors and distances
  have hY0 : 0 ≤ toReal Y := by linarith
  refine LinearSys.aux_steps (Ar := toRealMat A) hs hβX0 hβ hΔt hY0 hY hD hcurv N 0 ℓ₀ E₀ _ []
    (by omega) ?_ ?_ rfl (fun i hi => by simp at hi)
  · -- the errors of the rows carried
    intro q p hp
    rw [pow_zero, Matrix.vecMul_one]
    have h := Real.MatExp.weightedSum_vecMul_le hs (Lr q - toRealVec (ℓ₀ q))
      (exp (toReal Δt • toRealMat A) ^ p)
    refine le_trans h ?_
    rw [mul_comm (toReal Y)]
    exact mul_le_mul (hE₀ q) (hY p (by omega)) (norm_nonneg _) (hE0 q)
  · -- the distances at `t_0`
    intro q b hb
    rw [pow_zero, Matrix.vecMul_one]
    have hE : ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (mulUp Y (E₀ q)) := by
      refine le_trans (hE₀ q) (le_trans ?_ (mul_le_mulUp _ _))
      nlinarith [hE0 q]
    have h := LinearSys.dotProduct_le_verifySupportUpFloat c G hβX0 hβ (ℓ₀ q) hE hb
    exact le_trans (by linarith) (sub_le_subUp _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
