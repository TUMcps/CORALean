module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalFloat
public import CORALean.ContDynamics.LinearSysDT.Theorems.ErrMatFloatMem
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The float interval observer holds the true state

[1, Alg. 1]: every run `x_{k+1} = A x_k + u_k + ω_k` with `ω_k ∈ W`, measurements
`y_k = C x_k + v_k`, `v_k ∈ V` and initial error `x_0 - c ∈ R₀`, `c` the center of `R₀`, is in the
box `observeIntervalFloat` returns at every step. (The initial error is `x_0` minus the center,
which is what the real `observeInterval_outer` assumes, and which CORA's `Hinf-G` omits.) The
error obeys `e_{k+1} = (A - L C) e_k + (ω_k - L v_k)`; the three parts of its closed form are in
`R_x`, `R_wv`, and the nominal estimate is in its own box, with every quantity the real value of a
stored float. An outer statement.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `R_x` after `k` steps holds the initial error under `(A - L C)^k`
theorem LinearSysDT.aux_observeIntervalFloat_Rx (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) {M : Mat ℝ n n}
    (hM : M ∈ (LinearSysDT.errMatFloat sys.A L sys.C).construct)
    {e : Vec ℝ n} (he : e ∈ R₀.construct) (k : ℕ) : -- --- STMT ---
    (M ^ k) *ᵥ e ∈
      (sys.observeIntervalStateFloat L R₀ W V u y k).Rx.construct := by -- --- PROOF ---
  induction k with
  | zero => simpa [LinearSysDT.observeIntervalStateFloat] using he
  | succ k ih =>
    -- one more step maps the set through the interval matrix
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.mpr ⟨M, hM, _, ih, rfl⟩)

-- `D` after `k` steps holds the disturbance terms under `(A - L C)^k`
theorem LinearSysDT.aux_observeIntervalFloat_D (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) {M : Mat ℝ n n}
    (hM : M ∈ (LinearSysDT.errMatFloat sys.A L sys.C).construct)
    {d : Vec ℝ n}
    (hd : d ∈ ((Zonotope.mtimes (-L) V).plus W).construct) (k : ℕ) : -- --- STMT ---
    (M ^ k) *ᵥ d ∈
      (sys.observeIntervalStateFloat L R₀ W V u y k).D.construct := by -- --- PROOF ---
  induction k with
  | zero => simpa [LinearSysDT.observeIntervalStateFloat] using hd
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.mpr ⟨M, hM, _, ih, rfl⟩)

-- the boxed disturbance terms hold every sum `∑ (A - L C)^m d_m`
theorem LinearSysDT.aux_observeIntervalFloat_Rwv (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) {M : Mat ℝ n n}
    (hM : M ∈ (LinearSysDT.errMatFloat sys.A L sys.C).construct)
    (d : ℕ → Vec ℝ n)
    (hd : ∀ j, d j ∈ ((Zonotope.mtimes (-L) V).plus W).construct) (k : ℕ) : -- --- STMT ---
    ∑ m ∈ Finset.range k, (M ^ m) *ᵥ d m ∈
      (sys.observeIntervalStateFloat L R₀ W V u y k).Rwv.construct := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the empty sum is the origin, which the collected box starts at
    have h : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := by
      funext i
      simp [toRealVec, toReal_zero]
    rw [Finset.sum_range_zero, ← h]
    exact Interval.mem_point _
  | succ k ih =>
    -- the new term is in the box of `D` after `k` steps
    have hk : (M ^ k) *ᵥ d k ∈
        (sys.observeIntervalStateFloat L R₀ W V u y k).D.interval.construct :=
      Zonotope.interval_contains _ (LinearSysDT.aux_observeIntervalFloat_D sys L R₀ W V u y hM
        (hd k) k)
    rw [Finset.sum_range_succ]
    exact Interval.plus_outer _ _ ⟨_, ih, _, hk, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeIntervalFloat_outer (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) (x w : ℕ → Vec ℝ n) (v : ℕ → Vec ℝ sys.q)
    (h0 : x 0 - toRealVec R₀.c ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct)
    (hstep : ∀ k, x (k + 1) = toRealMat sys.A *ᵥ x k + toRealMat sys.B *ᵥ toRealVec (u k) + w k)
    (hy : ∀ k, toRealVec (y k) = toRealMat sys.C *ᵥ x k + v k) (k : ℕ) : -- --- STMT ---
    x k ∈ (sys.observeIntervalFloat L R₀ W V u y k).construct := by -- --- PROOF ---
  set M : Mat ℝ n n := toRealMat sys.A - toRealMat L * toRealMat sys.C with hMdef
  have hM := LinearSysDT.errMatFloat_mem sys.A L sys.C
  -- the disturbance terms `ω_j - L v_j` lie in `D`'s initial set `(-L) V ⊕ W`
  have hd : ∀ j, w j - toRealMat L *ᵥ v j ∈
      ((Zonotope.mtimes (-L) V).plus W).construct := fun j => by
    have hneg : toRealMat (-L) = -toRealMat L := toRealMat_neg _
    refine Zonotope.plus_outer _ _ ⟨toRealMat (-L) *ᵥ v j,
      Zonotope.mtimes_outer _ V ⟨v j, hv j, rfl⟩, w j, hw j, ?_⟩
    rw [hneg, Matrix.neg_mulVec]
    abel_nf
  -- the nominal estimate and the error's closed form, carried together
  have key : ∀ k, ∃ xh ∈ (sys.observeIntervalStateFloat L R₀ W V u y k).x.construct,
      ∃ ds : ℕ → Vec ℝ n,
        (∀ m, ds m ∈ ((Zonotope.mtimes (-L) V).plus W).construct) ∧
        x k = xh + ((M ^ k) *ᵥ (x 0 - toRealVec R₀.c) +
          ∑ m ∈ Finset.range k, (M ^ m) *ᵥ ds m) := by
    intro k
    induction k with
    | zero =>
      refine ⟨toRealVec R₀.c, Interval.mem_point R₀.c, fun m => w m - toRealMat L *ᵥ v m,
        fun m => hd m, ?_⟩
      simp
    | succ k ih =>
      obtain ⟨xh, hxh, ds, hds, hx⟩ := ih
      -- the next nominal estimate, `(A - L C) x̂ + B u + L y`
      refine ⟨M *ᵥ xh + toRealMat sys.B *ᵥ toRealVec (u k) + toRealMat L *ᵥ toRealVec (y k), ?_,
        fun m => Nat.casesOn m (w k - toRealMat L *ᵥ v k) (fun m => ds m),
        fun m => by cases m with | zero => exact hd k | succ m => exact hds m, ?_⟩
      · exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
          ⟨_, Interval.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.mpr ⟨M, hM, _, hxh, rfl⟩),
            _, Interval.mtimes_outer sys.B _ ⟨_, Interval.mem_point (u k), rfl⟩, rfl⟩, _,
          Interval.mtimes_outer L _ ⟨_, Interval.mem_point (y k), rfl⟩, rfl⟩
      · -- the error takes one more step through `A - L C`, and the new disturbance enters first
        have hsum : ∑ m ∈ Finset.range (k + 1), (M ^ m) *ᵥ
            (Nat.casesOn m (w k - toRealMat L *ᵥ v k) (fun m => ds m) : Vec ℝ n) =
            M *ᵥ (∑ m ∈ Finset.range k, (M ^ m) *ᵥ ds m) + (w k - toRealMat L *ᵥ v k) := by
          rw [Finset.sum_range_succ', Matrix.mulVec_sum]
          simp [Matrix.mulVec_mulVec, pow_succ']
        rw [hsum, pow_succ', ← Matrix.mulVec_mulVec, hstep k, hy k, hx, hMdef]
        simp only [Matrix.mulVec_add, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
        abel
  obtain ⟨xh, hxh, ds, hds, hx⟩ := key k
  -- the nominal box, plus the box of the error `R_x + R_wv`
  rw [hx]
  exact Interval.plus_outer _ _ ⟨xh, hxh, _, Interval.plus_outer _ _
    ⟨_, Zonotope.interval_contains _ (LinearSysDT.aux_observeIntervalFloat_Rx sys L R₀ W V u y hM
      h0 k), _, LinearSysDT.aux_observeIntervalFloat_Rwv sys L R₀ W V u y hM ds hds k, rfl⟩,
    rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
