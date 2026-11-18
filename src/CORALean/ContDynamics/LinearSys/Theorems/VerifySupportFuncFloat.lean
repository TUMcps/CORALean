module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportFuncFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.EnergyGrowthFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.LogNormUpFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySupportPassFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachImageAdd
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.MemInputReachIffSum
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyTimeSetdiff
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `LinearSys.verifySupportFuncFloat` is sound

A verdict `true` holds `(C_s C (e^{tA} x + y))_q < d_q` for every row `q`, time `t ∈ [0, t_f]`,
point `x` of `X₀ = c + G [-1, 1]^m` and everything `y` an input `u(s) ∈ B(u_c + G_U [-1, 1]^k)`
contributes by `t` (`LinearSys.inputReach`); a verdict `false` comes with a time, a row, a point
of `X₀` and a contribution that violate it there. A contribution is the constant part's plus the
varying part's (`LinearSys.inputReach_image_add`), over `[0, (i+1)Δt]` one per step carried by
`e^{jΔtA}` (`LinearSys.mem_inputReach_iff_sum`). Every time outside the unverified ones holds
every row (`LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff`); a pass removes only steps it
verified (`LinearSys.verifySupportPassFloat_sound`).

## Inputs
* `sys` – linear system, its `A` the system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `Cs` – float specification rows
* `Cm` – float output matrix
* `d` – float offsets
* `tFinal` – horizon
* `minStep` – smallest step
* `fuel` – passes at most

## Hypotheses
* `htf` – the horizon is nonnegative

## Conclusion
* verified: every row holds over `[0, t_f]` for all of `X₀` and every input; falsified: a point of
  `X₀` and an input violate the returned row at the returned time
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m p r q k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time in no interval of the fold over the flags is in none of `W` or in a flagged step. -/
private theorem LinearSys.aux_fold (Δt : ℚ) (q : Fin r) (t : ℝ) : -- --- CONCL ---
    ∀ (l : List ((Fin r → Bool) × ℕ)) (W : List (ℚ × ℚ)),
    (∀ iv ∈ l.foldl (fun W f => if f.1 q then LinearSys.verifyTimeSetdiff W (f.2 * Δt)
        ((f.2 + 1) * Δt) else W) W, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
    (∀ iv ∈ W, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) ∨ ∃ f ∈ l, f.1 q = true ∧
      (((f.2 * Δt : ℚ)) : ℝ) ≤ t ∧ t ≤ (((f.2 + 1) * Δt : ℚ) : ℝ) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro W h; exact Or.inl h
  | cons f l ih =>
    intro W h
    rcases ih _ h with h' | ⟨f', hf', hq, ht⟩
    · by_cases hfq : f.1 q = true
      · simp only [hfq, if_true] at h'
        by_cases hin : ∃ iv ∈ W, (iv.1 : ℝ) ≤ t ∧ t ≤ iv.2
        · obtain ⟨iv, hiv, ht⟩ := hin
          exact Or.inr ⟨f, List.mem_cons_self, hfq,
            LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff hiv ht h'⟩
        · push Not at hin
          exact Or.inl fun iv hiv h => absurd h.2 (not_le.mpr (hin iv hiv h.1))
      · simp only [hfq, Bool.false_eq_true, if_false] at h'
        exact Or.inl h'
    · exact Or.inr ⟨f', List.mem_cons_of_mem _ hf', hq, ht⟩

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- `e^{AΔt}` carried `k` times is the flow over `kΔt`. -/
private theorem LinearSys.aux_exp_pow' (A : Mat ℝ n n) (Δt : ℝ) (k : ℕ) :
    exp (((k : ℝ) * Δt) • A) = exp (Δt • A) ^ k := by
  have h1 : ((k : ℝ) * Δt) • A = k • (Δt • A) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [h1]
  exact Matrix.exp_nsmul k _

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The constant input's solution over `k` steps: one step's, carried by `e^{jhA}`, `j < k`. -/
private theorem LinearSys.aux_expIntegral_steps (A : Mat ℝ n n) {h : ℝ} (hh : 0 ≤ h)
    (v : Vec ℝ n) : -- --- CONCL ---
    ∀ k : ℕ, Real.MatExp.expIntegral A (k * h) *ᵥ v
      = ∑ j ∈ Finset.range k,
          exp (h • A) ^ j *ᵥ (Real.MatExp.expIntegral A h *ᵥ v) := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_mul, Real.MatExp.expIntegral_mulVec A v le_rfl,
      intervalIntegral.integral_same, Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, ← LinearSys.aux_exp_pow',
      show ((k + 1 : ℕ) : ℝ) * h = h + k * h by push_cast; ring,
      Real.MatExp.expIntegral_add_mulVec A v hh (by positivity)]
    abel

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- A row along a sum carried by powers of `e^{hA}`: the sum of the carried rows. -/
private theorem LinearSys.aux_dot_sum (A : Mat ℝ n n) (h : ℝ) (L : Vec ℝ n) (z : ℕ → Vec ℝ n)
    (k : ℕ) :
    L ⬝ᵥ (∑ j ∈ Finset.range k, exp (h • A) ^ j *ᵥ z j)
      = ∑ j ∈ Finset.range k, (L ᵥ* exp (h • A) ^ j) ⬝ᵥ z j := by
  rw [dotProduct_sum]
  exact Finset.sum_congr rfl fun j _ => dotProduct_mulVec _ _ _

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The varying input set `M [-1, 1]^k`: bounded, with the origin. -/
private theorem LinearSys.aux_U0 (M : Mat ℝ n k) :
    Bornology.IsBounded ((fun β => M *ᵥ β) '' Set.Icc (-1 : Fin k → ℝ) 1) ∧
      (0 : Vec ℝ n) ∈ (fun β => M *ᵥ β) '' Set.Icc (-1 : Fin k → ℝ) 1 := by
  refine ⟨(isCompact_Icc.image (Matrix.mulVecLin M).continuous_of_finiteDimensional).isBounded,
    0, ⟨fun c => by simp, fun c => by simp⟩, by simp⟩

omit [ToRat 𝕋] in
/-- What an input in `u₀ + M [-1, 1]^k` contributes by `t ∈ [ih, (i+1)h]`, along a row: the
constant part's solution carried from `ih` and over the steps before, and one varying
contribution per step `j ≤ i`. -/
private theorem LinearSys.aux_reach_decomp (sys : LinearSys 𝕋 n) (L : Vec ℝ n) (u0v : Vec ℝ n)
    (M : Mat ℝ n k) {h : ℝ} (hh : 0 ≤ h) (i : ℕ) {t : ℝ} (ht1 : i * h ≤ t) (ht2 : t ≤ (i + 1) * h)
    (x : Vec ℝ n) {y : Vec ℝ n}
    (hy : y ∈ sys.inputReach (S := ExactSet)
      ((fun z => u0v + z) '' ((fun β => M *ᵥ β) '' Set.Icc (-1) 1)) t) : -- --- CONCL ---
    ∃ zs : ℕ → Vec ℝ n, (∀ j < i + 1,
        zs j ∈ sys.inputReach (S := ExactSet) ((fun β => M *ᵥ β) '' Set.Icc (-1) 1) h) ∧
      L ⬝ᵥ (exp (t • Scalar.toRealMat sys.A) *ᵥ x + y)
        = L ⬝ᵥ (exp (t • Scalar.toRealMat sys.A) *ᵥ x)
          + (L ᵥ* exp (h • Scalar.toRealMat sys.A) ^ i) ⬝ᵥ
            (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (t - i * h) *ᵥ u0v)
          + ∑ j ∈ Finset.range i, (L ᵥ* exp (h • Scalar.toRealMat sys.A) ^ j) ⬝ᵥ
            (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) h *ᵥ u0v)
          + ∑ j ∈ Finset.range (i + 1), (L ᵥ* exp (h • Scalar.toRealMat sys.A) ^
              j) ⬝ᵥ zs j := by -- --- PROOF ---
  obtain ⟨hbdd, h0⟩ := LinearSys.aux_U0 M
  have hi0 : (0 : ℝ) ≤ i * h := by positivity
  have ht0 : 0 ≤ t := le_trans hi0 ht1
  rw [sys.inputReach_image_add hbdd ht0] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  -- the varying part, up to the step's end, one contribution per step
  have hmono := sys.inputReach_mono (S := ExactSet) hbdd h0 ht0
    (show t ≤ ((i + 1 : ℕ) : ℝ) * h by push_cast; exact ht2) hy₀
  obtain ⟨zs, hzs, hzeq⟩ := (sys.mem_inputReach_iff_sum (S := ExactSet) hh hbdd ⟨0, h0⟩ (i + 1)
    y₀).mp hmono
  refine ⟨zs, hzs, ?_⟩
  -- the constant part: carried from `ih`, and over the steps before
  have hconst : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) t *ᵥ u0v
      = exp (h • (Scalar.toRealMat sys.A)) ^ i *ᵥ (Real.MatExp.expIntegral (Scalar.toRealMat sys.A)
          (t - i * h) *ᵥ u0v)
        + ∑ j ∈ Finset.range i, exp (h • (Scalar.toRealMat sys.A)) ^ j *ᵥ (Real.MatExp.expIntegral
            (Scalar.toRealMat sys.A) h *ᵥ u0v) := by
    rw [← LinearSys.aux_expIntegral_steps (Scalar.toRealMat sys.A) hh u0v i, ←
        LinearSys.aux_exp_pow',
      ← Real.MatExp.expIntegral_add_mulVec (Scalar.toRealMat sys.A) u0v (by linarith) hi0]
    congr 1; ring
  have hz' : y₀ = ∑ j ∈ Finset.range (i + 1), exp (h • (Scalar.toRealMat sys.A)) ^ j *ᵥ zs j := by
    rw [hzeq]
    exact Finset.sum_congr rfl fun j _ => by rw [LinearSys.aux_exp_pow']
  dsimp only
  rw [hz', hconst, dotProduct_add, dotProduct_add, dotProduct_add, LinearSys.aux_dot_sum,
    LinearSys.aux_dot_sum, dotProduct_mulVec L (exp (h • Scalar.toRealMat sys.A) ^ i)]
  ring

omit [ToRat 𝕋] in
/-- And back: the constant part over `k` steps and one varying contribution per step are what an
input in `u₀ + M [-1, 1]^k` contributes by `kh`. -/
private theorem LinearSys.aux_reach_compose (sys : LinearSys 𝕋 n) (L : Vec ℝ n) (u0v : Vec ℝ n)
    (M : Mat ℝ n k) {h : ℝ} (hh : 0 ≤ h) (k' : ℕ) (x : Vec ℝ n) (zs : ℕ → Vec ℝ n)
    (hzs : ∀ j < k',
      zs j ∈ sys.inputReach (S := ExactSet) ((fun β => M *ᵥ β) '' Set.Icc (-1) 1)
          h) : -- --- CONCL ---
    ∃ y ∈ sys.inputReach (S := ExactSet)
        ((fun z => u0v + z) '' ((fun β => M *ᵥ β) '' Set.Icc (-1) 1)) (k' * h),
      L ⬝ᵥ (exp (((k' : ℝ) * h) • Scalar.toRealMat sys.A) *ᵥ x + y)
        = L ⬝ᵥ (exp (((k' : ℝ) * h) • Scalar.toRealMat sys.A) *ᵥ x)
          + ∑ j ∈ Finset.range k', (L ᵥ* exp (h • Scalar.toRealMat sys.A) ^ j) ⬝ᵥ
            (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) h *ᵥ u0v)
          + ∑ j ∈ Finset.range k', (L ᵥ* exp (h • Scalar.toRealMat sys.A) ^ j) ⬝ᵥ
              zs j := by -- --- PROOF ---
  obtain ⟨hbdd, h0⟩ := LinearSys.aux_U0 M
  have hk0 : (0 : ℝ) ≤ k' * h := by positivity
  set y₀ := ∑ j ∈ Finset.range k', exp (((j : ℝ) * h) • (Scalar.toRealMat sys.A)) *ᵥ zs j
  have hy₀ := (sys.mem_inputReach_iff_sum (S := ExactSet) hh hbdd ⟨0, h0⟩ k' y₀).mpr
    ⟨zs, hzs, rfl⟩
  refine ⟨Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (k' * h) *ᵥ u0v + y₀, ?_, ?_⟩
  · rw [sys.inputReach_image_add hbdd hk0]
    exact ⟨y₀, hy₀, rfl⟩
  · have hz' : y₀ = ∑ j ∈ Finset.range k', exp (h • (Scalar.toRealMat sys.A)) ^ j *ᵥ zs j :=
      Finset.sum_congr rfl fun j _ => by rw [LinearSys.aux_exp_pow']
    rw [hz', LinearSys.aux_expIntegral_steps (Scalar.toRealMat sys.A) hh u0v k', dotProduct_add,
        dotProduct_add,
      LinearSys.aux_dot_sum, LinearSys.aux_dot_sum]
    ring

/-- The passes: what a verdict claims holds as long as every time outside `U` holds every row. -/
private theorem LinearSys.aux_loop (sys : LinearSys 𝕋 n) {s c : Vec 𝕋 n} {G : Mat 𝕋 n m}
    {v : Vec 𝕋 n} {βX κ μ : 𝕋} {u₀ : Interval (Mat 𝕋 n 1)} {MU : Interval (Mat 𝕋 n k)}
    {ℓ₀ : Mat 𝕋 r n} {E₀ d : Vec 𝕋 r} {T : ℚ} {minStep : 𝕋}
    {Lr : Fin r → Vec ℝ n} {u0r : Mat ℝ n 1} {Mr : Mat ℝ n k} (hs : ∀ i, 0 < toReal (s i))
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i)) (hβX0 : 0 ≤ toReal βX)
    (hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i))
    (hμ : ∀ t : ℝ, 0 ≤ t → ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat sys.A))‖ ≤
      toReal κ * Real.exp (t * toReal μ))
    (hE₀ : ∀ q, ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (E₀ q))
    (hu : u0r ∈ u₀.toSet) (hM : Mr ∈ MU.toSet) : -- --- CONCL ---
    let Uset := (fun z => (fun l => u0r l 0) + z) '' ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1)
    ∀ fuel Δt (U : Fin r → List (ℚ × ℚ)) tf it,
    (∀ q (t : ℝ), 0 ≤ t → t ≤ T → (∀ iv ∈ U q, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
      ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ y ∈ sys.inputReach (S := ExactSet) Uset t,
      Lr q ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b) + y)
        < toReal (d q)) →
    ∀ R, R = LinearSys.step_verifySupportLoop sys.A s c G v βX κ μ u₀ MU ℓ₀ E₀ d T minStep fuel Δt
      U tf it →
    (R.verdict = some true → ∀ q (t : ℝ), 0 ≤ t → t ≤ T → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
      ∀ y ∈ sys.inputReach (S := ExactSet) Uset t,
      Lr q ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b) + y)
        < toReal (d q))
    ∧ (R.verdict = some false → ∃ t q, R.falsification = some (t, q) ∧ 0 ≤ t ∧ t ≤ T ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ ∃ y ∈ sys.inputReach (S := ExactSet) Uset t,
      toReal (d q) < Lr q ⬝ᵥ (exp ((t : ℝ) • toRealMat sys.A) *ᵥ
        (toRealVec c + toRealMat G *ᵥ b) + y))
    := by -- --- PROOF ---
  intro Uset fuel
  induction fuel with
  | zero => intro Δt U tf it _ R hR; subst hR; simp [LinearSys.step_verifySupportLoop]
  | succ fuel ih =>
    intro Δt U tf it hU R hR
    subst hR
    have hpass := LinearSys.verifySupportPassFloat_sound sys (Δt := Δt)
      (N := ⌈tf / ToRat.toRat Δt⌉₊) (T := T) (d := d) hs hv hβX0 hβX hμ hE₀ hu hM
    -- one pass, by its outcome: not converged, no bound, falsified, decided
    rw [LinearSys.step_verifySupportLoop]
    dsimp only
    split
    · next h => exact ih _ U tf _ hU _ rfl
    · simp
    -- a falsifying step: its time as a rational, its input composed
    · next k q h =>
      obtain ⟨hΔt, hT, h0, b, hb, zs, hzs, hviol⟩ := hpass.2 k q h
      refine ⟨by simp, fun _ => ⟨_, q, rfl, h0, hT, b, hb, ?_⟩⟩
      have hc : (((k : ℚ) * ToRat.toRat Δt : ℚ) : ℝ) = (k : ℝ) * toReal Δt := by
        push_cast; rw [ToRat.toReal_toRat]
      obtain ⟨y, hy, heq⟩ := LinearSys.aux_reach_compose sys (Lr q) (fun l => u0r l 0) Mr hΔt.le k
        (toRealVec c + toRealMat G *ᵥ b) zs hzs
      rw [hc]
      exact ⟨y, hy, lt_of_lt_of_eq hviol heq.symm⟩
    · next fl h =>
      obtain ⟨hΔt, _, hfl⟩ := hpass.1 fl h
      -- every time outside the new `U` holds every row
      have hU' : ∀ q (t : ℝ), 0 ≤ t → t ≤ T →
          (∀ iv ∈ LinearSys.step_verifySupportUnsat (ToRat.toRat Δt) fl U q,
            ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
          ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ y ∈ sys.inputReach (S := ExactSet) Uset t,
          Lr q ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b) + y)
            < toReal (d q) := by
        intro q t ht0 htT hnot b hb y hy
        simp only [LinearSys.step_verifySupportUnsat, Vector.getElem_ofFn] at hnot
        rcases LinearSys.aux_fold _ q t _ _ hnot with hW | ⟨f, hf, hq, ht1, ht2⟩
        · exact hU q t ht0 htT hW b hb y hy
        -- a flagged step holds the row by the pass's soundness
        · obtain ⟨hi, hfi⟩ := List.mem_zipIdx' (x := f.1) (i := f.2) hf
          have hc : ∀ j : ℕ, (((j : ℚ) * ToRat.toRat Δt : ℚ) : ℝ) = (j : ℝ) * toReal Δt := by
            intro j; push_cast; rw [ToRat.toReal_toRat]
          have hc1 : ((((f.2 : ℚ) + 1) * ToRat.toRat Δt : ℚ) : ℝ) = ((f.2 : ℝ) + 1) * toReal Δt :=
            by push_cast; rw [ToRat.toReal_toRat]
          rw [hc] at ht1
          rw [hc1] at ht2
          obtain ⟨zs, hzs, heq⟩ := LinearSys.aux_reach_decomp sys (Lr q) (fun l => u0r l 0) Mr
            hΔt.le f.2 ht1 ht2 (toRealVec c + toRealMat G *ᵥ b) hy
          exact lt_of_eq_of_lt heq (hfl f.2 hi q (hfi ▸ hq) t ht1 ht2 b hb zs hzs)
      -- all rows verified, the step too small, or the next pass
      split_ifs with hall hmin
      · refine ⟨fun _ q t ht0 htT b hb => hU' q t ht0 htT ?_ b hb, by simp⟩
        have := List.all_eq_true.mp hall q (List.mem_finRange q)
        rw [List.isEmpty_iff] at this
        simp [this]
      · simp
      · exact ih _ _ _ _ hU' _ rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySupportFuncFloat_sound (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) (Bm : Mat 𝕋 n q) (uc : Vec 𝕋 q) (GU : Mat 𝕋 q k) (Cs : Mat 𝕋 r p)
    (Cm : Mat 𝕋 p n) (d : Vec 𝕋 r) {tFinal : 𝕋} (minStep : 𝕋) (fuel : ℕ)
    (htf : 0 ≤ toReal tFinal) : -- --- CONCL ---
    let U := (fun β => toRealMat Bm *ᵥ (toRealVec uc + toRealMat GU *ᵥ β)) '' Set.Icc (-1) 1
    let res := LinearSys.verifySupportFuncFloat sys.A c G Bm uc GU Cs Cm d tFinal minStep fuel
    (res.verdict = some true →
      ∀ q (t : ℝ), 0 ≤ t → t ≤ toReal tFinal → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
      ∀ y ∈ sys.inputReach (S := ExactSet) U t,
      ((toRealMat Cs * toRealMat Cm) *ᵥ (exp (t • toRealMat sys.A) *ᵥ
        (toRealVec c + toRealMat G *ᵥ b) + y)) q < toReal (d q))
    ∧ (res.verdict = some false →
      ∃ t q, res.falsification = some (t, q) ∧ 0 ≤ t ∧ t ≤ ToRat.toRat tFinal ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧ ∃ y ∈ sys.inputReach (S := ExactSet) U t,
      toReal (d q) < ((toRealMat Cs * toRealMat Cm) *ᵥ (exp ((t : ℝ) • toRealMat sys.A) *ᵥ
        (toRealVec c + toRealMat G *ᵥ b) + y)) q) := by -- --- PROOF ---
  intro U res
  simp only [res]
  set Lr : Fin r → Vec ℝ n := fun q i => (toRealMat Cs * toRealMat Cm) q i
  have hLr : ∀ q (y : Vec ℝ n), ((toRealMat Cs * toRealMat Cm) *ᵥ y) q = Lr q ⬝ᵥ y :=
    fun _ _ => rfl
  simp only [hLr]
  have hT : ((ToRat.toRat tFinal : ℚ) : ℝ) = toReal tFinal := ToRat.toReal_toRat _
  -- the input in state space: `B u_c` and `B G_U`, each in its bracket
  set u0r : Mat ℝ n 1 := fun l _ => (toRealMat Bm *ᵥ toRealVec uc) l with hu0r
  set Mr : Mat ℝ n k := toRealMat Bm * toRealMat GU with hMr
  have hUeq : U = (fun z => (fun l => u0r l 0) + z) '' ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) := by
    simp only [U, Set.image_image]
    refine Set.image_congr fun β _ => ?_
    rw [Matrix.mulVec_add, hMr, ← Matrix.mulVec_mulVec]
  have hu : u0r ∈ (⟨matMulDown Bm fun j _ => uc j, matMulUp Bm fun j _ => uc j⟩ :
      Interval (Mat 𝕋 n 1)).toSet :=
    Interval.mem_mat_iff.mpr fun l c => ⟨dotDown_le (Bm l) fun j => uc j,
      le_dotUp (Bm l) fun j => uc j⟩
  have hM : Mr ∈ (⟨matMulDown Bm GU, matMulUp Bm GU⟩ : Interval (Mat 𝕋 n k)).toSet :=
    Interval.mem_mat_iff.mpr fun l c => ⟨dotDown_le (Bm l) fun j => GU j c,
      le_dotUp (Bm l) fun j => GU j c⟩
  rw [hUeq]
  -- the run constants, named as the definition names them
  unfold LinearSys.verifySupportFuncFloat
  dsimp only
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
  set s := MatExp.balanceScalesFloat sys.A
  set v : Vec 𝕋 n := fun i => addUp (absolute (c i)) (sumUp fun j => absolute (G i j))
  set βX := maximum FloatOps.zero (maximumOver fun i => divUp (v i) (s i))
  set L := Interval.matMul (Interval.point Cs) (Interval.point Cm)
  set E₀ : Vec 𝕋 r := fun q => sumUp fun j => mulUp (subUp (L.sup q j) (L.inf q j)) (s j)
  split_ifs with hsc
  · simp
  -- past the check of the scales: they are positive
  have hs : ∀ i, 0 < toReal (s i) := by
    intro i
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_finRange,
      forall_const] at hsc
    have := toReal_lt_of_ltStrict (hsc i)
    rwa [toReal_zero] at this
  -- the run constants meet the pass's hypotheses
  have hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i) := by
    intro i
    have h1 := add_le_addUp (absolute (c i)) (sumUp fun j => absolute (G i j))
    have h2 := sum_le_sumUp (fun j => absolute (G i j))
    simp only [toReal_absolute] at h1 h2
    show _ ≤ toReal (addUp (absolute (c i)) (sumUp fun j => absolute (G i j)))
    linarith
  have hβX0 : 0 ≤ toReal βX := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i) := by
    intro i
    have hdiv := div_le_divUp (v i) (s i) (hs i)
    rw [div_le_iff₀ (hs i)] at hdiv
    refine le_trans hdiv (mul_le_mul_of_nonneg_right ?_ (hs i).le)
    rw [toReal_maximum]
    exact le_trans (le_maximumOver (fun i => divUp (v i) (s i)) i) (le_max_right _ _)
  -- the growth rate, and the rows' bracket with its error
  have hμ : ∀ t : ℝ, 0 ≤ t → ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat sys.A))‖ ≤
      toReal (LinearSys.step_verifySupportGrowth sys.A s tFinal).1 *
        Real.exp (t * toReal (LinearSys.step_verifySupportGrowth sys.A s tFinal).2) := by
    intro t ht
    unfold LinearSys.step_verifySupportGrowth
    dsimp only
    -- the log norm, or an accepted energy weight
    rcases hκ : MatExp.energyGrowthFloat sys.A s (divUp FloatOps.one tFinal) with _ | κ
    · rw [toReal_one, one_mul]
      exact MatExp.norm_scaleConj_exp_le_logNormUpFloat sys.A hs ht
    · exact MatExp.norm_scaleConj_exp_le_energyGrowthFloat sys.A _ hs κ (Option.mem_def.mpr hκ) t ht
  have hL : toRealMat Cs * toRealMat Cm ∈ L.toSet :=
    Interval.matMul_outer _ _ (Interval.mem_point Cs) (Interval.mem_point Cm)
  have hE₀ : ∀ q, ∑ i, |Lr q i - toReal (L.sup q i)| * toReal (s i) ≤ toReal (E₀ q) := by
    intro q
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
    obtain ⟨hlo, hhi⟩ := Interval.mem_mat_iff.mp hL q i
    have h1 := sub_le_subUp (L.sup q i) (L.inf q i)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (hs i).le) (mul_le_mulUp _ _)
    rw [abs_sub_comm, abs_of_nonneg (by simp only [Lr]; linarith)]
    simp only [Lr]; linarith
  have hloop := LinearSys.aux_loop sys hs hv hβX0 hβX hμ hE₀ hu hM (minStep := minStep)
    (T := ToRat.toRat tFinal) (d := d)
  split
  · -- `X₀` itself violates a row, with the input held at zero time
    next q hfind =>
    refine ⟨by simp, fun _ => ⟨0, q, rfl, le_rfl, ?_, ?_⟩⟩
    · rw [← hT] at htf
      exact_mod_cast htf
    · have hlow := List.find?_some hfind
      have hpos : 0 < toReal (subDown (LinearSys.verifySupportDownFloat c G βX (L.sup q) (E₀ q))
          (d q)) := by
        have := toReal_lt_of_ltStrict hlow
        rwa [toReal_zero] at this
      -- a point of `X₀` below the lower distance, and the input at zero time
      have hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i) :=
        fun i => le_trans (hv i) (hβX i)
      obtain ⟨b, hb, hle⟩ := LinearSys.exists_le_dotProduct_verifySupportDownFloat c G hβX0 hβ
        (L.sup q) (hE₀ q)
      have hsub := subDown_le_sub (LinearSys.verifySupportDownFloat c G βX (L.sup q) (E₀ q)) (d q)
      obtain ⟨y, hy, heq⟩ := LinearSys.aux_reach_compose sys (Lr q) (fun l => u0r l 0) Mr le_rfl 0
        (toRealVec c + toRealMat G *ᵥ b) (fun _ => 0) (fun j hj => absurd hj (Nat.not_lt_zero j))
      -- at `t = 0` the flow is the identity and the input adds nothing
      simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty, add_zero] at heq hy
      refine ⟨b, hb, y, by simpa using hy, ?_⟩
      rw [Rat.cast_zero]
      refine lt_of_lt_of_eq ?_ heq.symm
      rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
      linarith
  · -- the passes from `U = [0, t_f]`
    obtain ⟨h1, h2⟩ := hloop fuel _ (fun _ => [(0, ToRat.toRat tFinal)]) (ToRat.toRat tFinal) 0
      (fun q t ht0 htT hnot => (hnot _ List.mem_cons_self
        ⟨by simpa using ht0, by simpa using htT⟩).elim) _ rfl
    exact ⟨fun h q t ht0 htT => h1 h q t ht0 (hT ▸ htT), h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
