module

public import CORALean.ContDynamics.LinearSys.Definitions.AutoInvariantFloat
public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Operations.AutoStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AffineWindowFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetSplitFloat
public import CORALean.ContDynamics.LinearSys.Theorems.SquaringsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecenter
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# One `Alg. 2` iteration keeps its invariant and its window holds every run

From a state holding `AutoInvariantFloat`, `autoStepFloat` returns one holding it `Δt_k` later,
and a window `R̂(τ_k)` holding every run over `[t_k, t_{k+1}]`. The step asks nothing of the
tuning: `autoStepFloat` checks the pair `(Δt_k, η_k)` it returns, so a step that ran is one at
an admissible pair, whichever way `autoTuneDeltaTFloat` and `autoTuneSetOrder` picked it.

The free motion and the constant input's share, from `H(t_k)`, are in the affine window
(`affineWindowFloat_outer`, lines 27-28). The `Ũ`-input's share by `t_{k+1}` comes apart at
`t_k` (`inputReach_separation_subset`), its newest step is in `bPU_0 ⊕ bPU_∞`
(`inputReach_subset_split_float`), and `e^{At_k}` carries the halves to `P̂^U_0` and into the box
of `P̂^U_∞` (lines 17-18). The window's `P̂^U(t_{k+1})` reduces `P̂^U_0` and keeps `P̂^U_∞`
(line 23).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An iteration from a state holding the invariant reaches one holding it later in time, and
its window holds every run over `[t_k, t_{k+1}]`. -/
theorem LinearSys.autoStepFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)} {tend : 𝕋}
    {εmax ζ : ℚ} {ηmax fuel : ℕ} {s s' : LinearSys.AutoStateFloat 𝕋 n} {R : Zonotope (Vec 𝕋 n)}
    (h : sys.autoStepFloat X₀ V tend εmax ζ ηmax fuel s = some (s', R))
    (hinv : sys.AutoInvariantFloat X₀ V s) :
    sys.AutoInvariantFloat X₀ V s' ∧ s.t < s'.t ∧
      ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
        sys.CanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
        U ⊆ V.construct → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ T →
          x t ∈ R.construct := by -- --- PROOF ---
  obtain ⟨h0, hlo, hhi, hH, hPu, hPU⟩ := hinv
  unfold LinearSys.autoStepFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sq, hsq, ⟨Δt, η⟩, -, h⟩ := h
  dsimp only at h
  split_ifs at h with hcheck
  obtain ⟨hΔ, hη2, hnrm, -, -⟩ := hcheck
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨sq1, hsq1, ρ, hρ, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set A := Scalar.toRealMat sys.A with hA
  set eAtk := sys.expSquaringFloat s.tLo s.tHi (max ηmax 2) sq with heAtk
  set ũ := Recenter.center V with hũ
  set Ũ := Recenter.recenter V with hŨ
  set tk : ℝ := (s.t : ℝ) with htk
  have htk0 : 0 ≤ tk := by rw [htk]; exact_mod_cast h0
  have hΔr : 0 < toReal Δt := by rw [← ToRat.toReal_toRat]; exact_mod_cast hΔ
  -- the order the check admitted, read back from ℚ
  have hadm : sys.OrderAdmissibleFloat Δt Δt η := ⟨hη2, by
    have h := (Rat.cast_le (K := ℝ)).mpr hnrm
    push_cast at h
    rwa [← ToRat.toReal_toRat]⟩
  have hΔq : ((ToRat.toRat Δt : ℚ) : ℝ) = toReal Δt := ToRat.toReal_toRat Δt
  have ht' : (((s.t + ToRat.toRat Δt : ℚ)) : ℝ) = toReal Δt + tk := by
    push_cast; rw [hΔq]; ring
  -- `[e^{At_k}] Z` and `[e^{At_{k+1}}] Z` hold `e^{At_k} z` and `e^{At_{k+1}} z`
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (tk • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAtk Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAtk Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec (le_max_right _ _) hsq) hlo hhi)
        (Set.mem_image_of_mem _ hz))
  have hmt1 : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct
      → exp ((toReal Δt + tk) • A) *ᵥ z
        ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋])
          (sys.expSquaringFloat (addDown s.tLo Δt) (addUp s.tHi Δt) η sq1) Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec hη2 hsq1)
        ((addDown_le_add _ _).trans (by linarith)) (le_trans (by linarith) (add_le_addUp _ _)))
        (Set.mem_image_of_mem _ hz))
  -- `{ũ}` holds what it is built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  -- the constant `ũ` held over `[0, τ]` is an admissible input of any set holding `ũ`
  have hconst : ∀ {W : Zonotope (Vec 𝕋 n)}, ũ ∈ W.construct → ∀ {τ : ℝ}, 0 ≤ τ →
      Real.MatExp.expIntegral A τ *ᵥ ũ ∈ sys.inputReach (S := 𝒵[𝕋]) W τ :=
    fun hW _ hτ => ⟨fun _ => ũ, fun _ _ => hW, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ hτ).symm⟩
  have hPuΔ := sys.inputReach_subset_inputSolutionFloat hΔr hadm _ (hconst hpt hΔr.le)
  have hsplit := sys.inputReach_subset_split_float hΔr hadm Ũ
  -- the `Ũ`-input's share by `t_k + Δt`, in the two halves of eq. (27)
  have hPU' : ∀ y ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ (toReal Δt + tk),
      y ∈ (s.PU0 ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAtk
          (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
            (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) Ũ)).construct
        + (s.PUinf ⊞ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (sys.inputTaylorSumTailFloat Δt Ũ η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
            (𝕄 := ℐ[𝕋])
            (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) Ũ)).interval.zonotope
          ).construct := by
    -- split `y` at `t_k` and send each part to its summand
    intro y hy
    obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩ := sys.inputReach_separation_subset hΔr.le
      htk0 (CompactSet.isBounded_construct Ũ) hy
    obtain ⟨q0, hq0, qi, hqi, rfl⟩ := hPU q hq
    obtain ⟨p0, hp0, pi, hpi, rfl⟩ := hsplit hp
    refine ⟨q0 + exp (tk • A) *ᵥ p0, Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add hq0 (hmt hp0)),
      qi + exp (tk • A) *ᵥ pi, Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hqi
        (Interval.zonotope_contains _ (Zonotope.interval_contains _ (hmt hpi)))), ?_⟩
    beta_reduce; rw [Matrix.mulVec_add]; abel
  -- the constant's share by `t_{k+1}`, in the box `P^u(t_{k+1})`
  have hPu' : Real.MatExp.expIntegral A (toReal Δt + tk) *ᵥ ũ
      ∈ ((s.Pu.zonotope ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAtk
        (sys.inputSolutionFloat Δt η (Interval.point V.c).zonotope)).interval).construct := by
    rw [Real.MatExp.expIntegral_add_mulVec A ũ hΔr.le htk0, add_comm]
    exact Zonotope.interval_contains _ (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (Interval.zonotope_contains _ hPu) (hmt hPuΔ)))
  -- `H(t_{k+1})` holds the affine flow from `X₀`
  have hH' : ∀ x₀ ∈ X₀.construct, exp ((toReal Δt + tk) • A) *ᵥ x₀
      + Real.MatExp.expIntegral A (toReal Δt + tk) *ᵥ ũ ∈
        (Mtimes.mtimes (S := 𝒵[𝕋])
        (𝕄 := ℐ[𝕋])
        (sys.expSquaringFloat (addDown s.tLo Δt) (addUp s.tHi Δt) η sq1) X₀
        ⊞ ((s.Pu.zonotope ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (sys.inputSolutionFloat Δt η (Interval.point V.c).zonotope)).interval).zonotope
        ).construct := fun x₀ hx₀ =>
    Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (hmt1 hx₀) (Interval.zonotope_contains _ hPu'))
  -- the invariant at `t_{k+1}`, field by field, then the time and the window
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((s.t + ToRat.toRat Δt : ℚ) : ℝ) := by rw [ht']; linarith
    exact_mod_cast this
  · show toReal (addDown s.tLo Δt) ≤ _
    rw [ht']; exact (addDown_le_add _ _).trans (by linarith)
  · show _ ≤ toReal (addUp s.tHi Δt)
    rw [ht']; exact le_trans (by linarith) (add_le_addUp _ _)
  · intro x₀ hx₀
    rw [ht']
    exact hH' x₀ hx₀
  · rw [ht']; exact hPu'
  · intro y hy
    rw [ht'] at hy
    exact hPU' y hy
  · show s.t < s.t + ToRat.toRat Δt
    linarith
  -- the window: the run is the affine flow from `H(t_k)` plus its departure from it
  · intro T U x u traj hUV t ht htT
    rw [ht'] at ht
    have ht0 : 0 ≤ t := htk0.trans ht.1
    set τ := t - tk with hτ
    have hτ0 : 0 ≤ τ := sub_nonneg.mpr ht.1
    have hτΔ : τ ≤ toReal Δt := by linarith [ht.2]
    -- the run's departure from the affine flow by `t`, inside the input's share by `t_{k+1}`
    have hd := traj.sub_mem_inputReach_recenter (S' := 𝒵[𝕋]) (V := V)
      hUV ⟨ht0, htT⟩
    have hd' := sys.inputReach_mono (S := 𝒵[𝕋])
      (CompactSet.isBounded_construct Ũ)
      (Recenter.zero_mem_recenter V) ht0 ht.2 hd
    obtain ⟨d0, hd0, di, hdi, hdeq⟩ := hPU' _ hd'
    -- the affine flow from `H(t_k)`: where its point `x_k` is one step on is in `H(t_{k+1})`
    have hxk := hH (x 0) traj.init
    have hnext : exp (toReal Δt • A) *ᵥ (exp (tk • A) *ᵥ x 0 + Real.MatExp.expIntegral A tk *ᵥ ũ)
        + Real.MatExp.expIntegral A (toReal Δt) *ᵥ ũ ∈
          (Mtimes.mtimes (S := 𝒵[𝕋])
          (𝕄 := ℐ[𝕋])
          (sys.expSquaringFloat (addDown s.tLo Δt) (addUp s.tHi Δt) η sq1) X₀
          ⊞ ((s.Pu.zonotope ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
            (S := 𝒵[𝕋]) eAtk
            (sys.inputSolutionFloat Δt η (Interval.point V.c).zonotope)).interval).zonotope
          ).construct := by
      -- both the exponential and the integral split at `t_k`, so `x_k` one step on is `t_{k+1}`'s
      have hG := Real.MatExp.expIntegral_add_mulVec A ũ htk0 hΔr.le
      have hE : exp ((toReal Δt + tk) • A) = exp (toReal Δt • A) * exp (tk • A) := by
        rw [add_smul]
        exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
      have := hH' (x 0) traj.init
      rw [hE, add_comm (toReal Δt) tk, hG, ← Matrix.mulVec_mulVec] at this
      rwa [Matrix.mulVec_add, add_assoc]
    -- the affine window holds the flow over `[0, τ]` from `x_k`
    have hwin := sys.affineWindowFloat_outer (ũ := V.c) hΔr hadm hxk hnext hτ0 hτΔ
    have hexp : exp (t • A) = exp (τ • A) * exp (tk • A) := by
      rw [show t = τ + tk by ring, add_smul]
      exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
    -- the run at `t` is the flow from `x_k` over `τ`, plus its departure from the free motion
    have hx : x t = (exp (τ • A) *ᵥ (exp (tk • A) *ᵥ x 0 + Real.MatExp.expIntegral A tk *ᵥ ũ)
        + Real.MatExp.expIntegral A τ *ᵥ ũ)
        + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)) := by
      rw [show Real.MatExp.expIntegral A t *ᵥ ũ = Real.MatExp.expIntegral A (tk + τ) *ᵥ ũ by
          rw [show tk + τ = t by ring],
        Real.MatExp.expIntegral_add_mulVec A ũ htk0 hτ0, hexp, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add]
      abel
    -- the departure, in `P̂^U(t_{k+1})`: `P̂^U_0` reduced, `P̂^U_∞` kept
    have hPUk1 : x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ) ∈ (Reduce.reduce
        (s.PU0 ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
            (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) Ũ)) ρ
        ⊞ (s.PUinf ⊞ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (sys.inputTaylorSumTailFloat Δt Ũ η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
            (𝕄 := ℐ[𝕋])
            (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) Ũ)).interval.zonotope)
        ).construct := by
      rw [← hdeq]
      exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add (Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _ hd0) hdi)
    rw [hx]
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hwin hPUk1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
