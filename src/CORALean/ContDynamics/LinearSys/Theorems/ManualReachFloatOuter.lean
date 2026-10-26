module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinearSys.Operations.ManualReachFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsManualInvariantFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.SquaringsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachRecenter
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `manualReachFloat` holds every run over every window

[1, Alg. 1] in floats from `aux_manualInitFloat`, which holds the invariant at `t₀ = 0`: `H(0)`
is `X₀` itself, and the constant and the `Ũ`-input have contributed `0`, which `{0}` holds.
`aux_manualRunFloat_outer` does the rest, at the order `reachOrderFloat` admitted. Every input
`u(t) ∈ B U + c` is in `V = B U ⊕ c`'s float enclosure.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Hypotheses
* none

## Conclusion
* every run is in the window of its time

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}
open MeasureTheory Pointwise
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- An iteration from a state holding the invariant reaches one holding it `Δt` later, and
its window holds every run over `[t_k, t_{k+1}]`. -/
private theorem LinearSys.aux_manualStepFloat_outer (sys : LinearSys 𝕋 n)
    {X₀ V : Zonotope (Vec 𝕋 n)} {Δt : 𝕋}
    {η ρ : ℕ} {s : LinearSys.ManualStateFloat 𝕋 n} (hΔt : 0 < toReal Δt)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η)
    (hinv : sys.IsManualInvariantFloat X₀ V s) : -- --- CONCL ---
    ∀ s' R, (s', R) ∈ sys.aux_manualStepFloat X₀ V Δt η ρ s →
      sys.IsManualInvariantFloat X₀ V s' ∧ (s'.t : ℝ) = s.t + toReal Δt ∧
        ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
          U ⊆ V.construct → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ T →
            x t ∈ R.construct := by -- --- PROOF ---
  intro s' R (h : sys.aux_manualStepFloat X₀ V Δt η ρ s = some (s', R))
  obtain ⟨h0, hlo, hhi, hH, hPu, hPU⟩ := hinv
  unfold LinearSys.aux_manualStepFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sq, hsq, sq1, hsq1, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set A := Scalar.toRealMat sys.A with hA
  set ũ := Recenter.center V with hũ
  set Ũ := Recenter.recenter V with hŨ
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  set tk : ℝ := (s.t : ℝ) with htk
  have htk0 : 0 ≤ tk := by rw [htk]; exact_mod_cast h0
  have hΔq : ((ToRat.toRat Δt : ℚ) : ℝ) = toReal Δt := ToRat.toReal_toRat Δt
  have ht' : (((s.t + ToRat.toRat Δt : ℚ)) : ℝ) = toReal Δt + tk := by
    push_cast; rw [hΔq]; ring
  -- `[e^{At_k}] Z` and `[e^{At_{k+1}}] Z` hold `e^{At_k} z` and `e^{At_{k+1}} z`
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (tk • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (sys.expSquaringFloat s.tEnc.inf s.tEnc.sup η sq) Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec hη.1 _ hsq) hlo hhi) (Set.mem_image_of_mem _ hz))
  -- the same at `t_{k+1}`, inside the bracket `[tLo ⊖ Δt, tHi ⊕ Δt]`
  have hmt1 : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct
      → exp ((toReal Δt + tk) • A) *ᵥ z
        ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋])
          (sys.expSquaringFloat (addDown s.tEnc.inf Δt) (addUp s.tEnc.sup Δt) η sq1) Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec hη.1 _ hsq1)
        ((addDown_le_add _ _).trans (by linarith)) (le_trans (by linarith) (add_le_addUp _ _)))
        (Set.mem_image_of_mem _ hz))
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant `ũ` held over `[0, τ]` is an admissible input of any set holding `ũ`
  have hconst : ∀ {W : Zonotope (Vec 𝕋 n)}, ũ ∈ W.construct → ∀ {τ : ℝ}, 0 ≤ τ →
      Real.MatExp.expIntegral A τ *ᵥ ũ ∈ sys.inputReach (S := 𝒵[𝕋]) W τ :=
    fun hW _ hτ => ⟨fun _ => ũ, fun _ _ => hW, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ hτ).symm⟩
  -- one step's shares, the constant's and the `Ũ`-input's, in their float input solutions
  have hPuΔ := sys.inputReach_subset_inputSolutionFloat hΔt hη _ (hconst hpt hΔt.le)
  have hPUΔ := sys.inputReach_subset_inputSolutionFloat hΔt hη Ũ
  -- the `Ũ`-input's share by `t_k + Δt` comes apart at `t_k`, and so does the constant's
  have hPU' : ∀ y ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ (toReal Δt + tk),
      y ∈ (Reduce.reduce (s.PU ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (sys.expSquaringFloat s.tEnc.inf s.tEnc.sup η sq) (sys.inputSolutionFloat Δt η Ũ))
        ρ).construct := by
    intro y hy
    obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩ := sys.inputReach_separation_subset hΔt.le
      htk0 (CompactSet.isBounded_construct Ũ) hy
    refine Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ ?_)
    have hmem := Set.add_mem_add (hPU q hq) (hmt (hPUΔ hp))
    rwa [add_comm q] at hmem
  -- the constant's share by `t_{k+1}`, in the box `P^u(t_{k+1})`
  have hPu' : Real.MatExp.expIntegral A (toReal Δt + tk) *ᵥ ũ
      ∈ (s.Pu.zonotope ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (sys.expSquaringFloat s.tEnc.inf s.tEnc.sup η sq)
        (sys.inputSolutionFloat Δt η (Interval.point V.c).zonotope)).interval.construct := by
    rw [Real.MatExp.expIntegral_add_mulVec A ũ hΔt.le htk0, add_comm]
    exact Zonotope.interval_contains _ (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (Interval.zonotope_contains _ hPu) (hmt hPuΔ)))
  -- the invariant at `t_{k+1}`, the time, then the window
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [ht']; ring, ?_⟩
  · have : (0 : ℝ) ≤ ((s.t + ToRat.toRat Δt : ℚ) : ℝ) := by rw [ht']; linarith
    exact_mod_cast this
  · rw [ht']; exact (addDown_le_add _ _).trans (by linarith)
  · rw [ht']; exact le_trans (by linarith) (add_le_addUp _ _)
  · intro x₀ hx₀
    rw [ht']
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (hmt1 hx₀) (Interval.zonotope_contains _ hPu'))
  · rw [ht']; exact hPu'
  · intro y hy
    rw [ht'] at hy
    exact hPU' y hy
  · intro T U x u traj hUV t ht htT
    rw [ht'] at ht
    have ht0 : 0 ≤ t := htk0.trans ht.1
    set τ := t - tk with hτ
    have hτ0 : 0 ≤ τ := sub_nonneg.mpr ht.1
    have hτΔ : τ ≤ toReal Δt := by linarith [ht.2]
    -- the run's departure from the free motion and the constant's share, by `t_{k+1}`
    have hd := traj.sub_mem_inputReach_recenter (S' := 𝒵[𝕋]) (V := V)
      hUV ⟨ht0, htT⟩
    have hd' := sys.inputReach_mono (S := 𝒵[𝕋])
      (CompactSet.isBounded_construct Ũ)
      (Recenter.zero_mem_recenter V) ht0 ht.2 hd
    -- the free motion and the constant over `[0, τ]` from `H(t_k)`
    have hcore := sys.timeIntervalFloat_outer hΔt hη s.H (hH (x 0) traj.init) hτ0 hτΔ
    have hc := sys.inputReach_subset_inputSolutionFloat hΔt hη seg
      (sys.inputReach_mono (S := 𝒵[𝕋])
        (CompactSet.isBounded_construct seg) h0seg hτ0 hτΔ
        (hconst hũseg hτ0))
    -- the time splits as `t = τ + t_k`, so the exponentials factor
    have hexp : exp (t • A) = exp (τ • A) * exp (tk • A) := by
      rw [show t = τ + tk by ring, add_smul]
      exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
    have hx : x t = (exp (τ • A) *ᵥ (exp (tk • A) *ᵥ x 0 + Real.MatExp.expIntegral A tk *ᵥ ũ)
        + Real.MatExp.expIntegral A τ *ᵥ ũ)
        + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)) := by
      rw [show Real.MatExp.expIntegral A t *ᵥ ũ = Real.MatExp.expIntegral A (tk + τ) *ᵥ ũ by
          rw [show tk + τ = t by ring],
        Real.MatExp.expIntegral_add_mulVec A ũ htk0 hτ0, hexp, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add]
      abel
    -- the three parts, each in its float window
    rw [hx]
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hcore hc)) (hPU' _ hd'))

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}

/-- `K` iterations from a state holding the invariant return `K` windows, the `j`-th holding
every run over `[t_k + jΔt, t_k + (j+1)Δt]`. -/
private theorem LinearSys.aux_manualRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {Δt : 𝕋} {η ρ : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η) : -- --- CONCL ---
    ∀ {K : ℕ} {s : LinearSys.ManualStateFloat 𝕋 n} {Rs : List (Zonotope (Vec 𝕋 n))},
      sys.aux_manualRunFloat X₀ V Δt η ρ K s = some Rs → sys.IsManualInvariantFloat X₀ V s →
      Rs.length = K ∧ ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
        sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
        U ⊆ V.construct → ∀ (j : ℕ) (hj : j < Rs.length),
          ∀ t ∈ Set.Icc ((s.t : ℝ) + j * toReal Δt) (s.t + (j + 1) * toReal Δt), t ≤ T →
            x t ∈ Rs[j].construct := by -- --- PROOF ---
  intro K
  induction K with
  | zero =>
    intro s Rs h _
    obtain rfl := (Option.some.inj h).symm
    exact ⟨rfl, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ K ih =>
    intro s Rs h hinv
    simp only [LinearSys.aux_manualRunFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s', R⟩, hstep, Rs', hrest, h⟩ := h
    obtain rfl := (Option.some.inj h).symm
    -- one iteration, then the rest of the run from the state it reached
    obtain ⟨hinv', ht', hwin⟩ := sys.aux_manualStepFloat_outer hΔt hη hinv _ _ hstep
    obtain ⟨hlen, hsnd⟩ := ih hrest hinv'
    refine ⟨by simp [hlen], fun {T U x u} traj hUV j hj t ht htT => ?_⟩
    cases j with
    | zero =>
      exact hwin traj hUV t ⟨by simpa using ht.1, by rw [ht']; simpa using ht.2⟩ htT
    | succ j =>
      have hj' : j < Rs'.length := by simpa using hj
      refine hsnd traj hUV j hj' t ⟨?_, ?_⟩ htT
      · rw [ht']; push_cast at ht; linarith [ht.1]
      · rw [ht']; push_cast at ht; linarith [ht.2]

end


omit [ToRat 𝕋] in
/-- `aux_manualInitFloat` holds what a state owes at `t₀ = 0`. -/
private theorem LinearSys.aux_manualInvariantFloat_init (sys : LinearSys 𝕋 n)
    (X₀ V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    sys.IsManualInvariantFloat X₀ V (LinearSys.aux_manualInitFloat X₀) := by -- --- PROOF ---
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have hΓ0 : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) 0 = 0 := by
    simp [Real.MatExp.expIntegral]
  refine ⟨le_rfl, by simp [LinearSys.aux_manualInitFloat, toReal_zero],
    by simp [LinearSys.aux_manualInitFloat, toReal_zero], fun x hx => ?_, ?_, fun y hy => ?_⟩
  · simpa [LinearSys.aux_manualInitFloat, hΓ0] using hx
  · have h0 := Interval.mem_point (fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [LinearSys.aux_manualInitFloat, hΓ0] using h0
  · obtain ⟨u, -, -, rfl⟩ := hy
    simpa [LinearSys.aux_manualInitFloat] using hzero


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U + c` is, at every
time of window `k`, in the `k`-th set. -/
theorem LinearSys.manualReachFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ sys.manualReachFloat params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
              params.U.construct) x u →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (h : sys.manualReachFloat params options = some Rs)
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.manualReachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', h⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  set V := sys.inputSetFloat U with hV
  obtain ⟨hlen, hsnd⟩ := sys.aux_manualRunFloat_outer hΔt hadm h
    (sys.aux_manualInvariantFloat_init X₀ V)
  refine ⟨N, hNΔt, hlen, fun {x u} traj k hk t ht => ?_⟩
  -- the run's inputs `B u + c` are in `B U ⊕ c`'s float enclosure
  have hUV : (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
      U.construct ⊆ ContSet.construct V :=
    sys.inputSetFloat_outer U
  have hkN : (k : ℝ) + 1 ≤ N := by rw [hlen] at hk; exact_mod_cast hk
  refine hsnd traj hUV k hk t ⟨by simpa [LinearSys.aux_manualInitFloat] using ht.1,
    by simpa [LinearSys.aux_manualInitFloat] using ht.2⟩ ?_
  rw [← hNΔt]
  exact ht.2.trans (mul_le_mul_of_nonneg_right hkN hΔt.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
