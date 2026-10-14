module

public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveInvariant
public import CORALean.ContDynamics.LinearSys.Operations.AdaptiveStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.SquaringsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# One adaptive float step keeps what the state owes, and holds every run

Lines 5-10 of [1, Alg. 1]: whatever `Alg. 2` and `Alg. 3` chose, the step is a
positive `Δt` at an admissible order. A run at `t = t_i + τ` is
`e^{At_i}(e^{Aτ} x₀ + Γ(τ) ũ + p) + (Γ(t_i) ũ + q)`, where the `Ũ`-input's
share by `t_{i+1}` comes apart at `t_i` (`inputReach_separation_subset`) into
`e^{At_i} p + q`: the bracket is in `[e^{At_i}](HR₀ ⊕ P̃^R ⊕ PR)`, the rest in
`P(t_i)` by the invariant. The same split at `t_{i+1}` carries the invariant on.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A step from a state holding the invariant reaches a state holding it, later
in time, and its window holds every run over `[t_i, t_{i+1}] ∩ [0, t_f]`. -/
theorem LinearSys.adaptiveStepFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {t₀ tf : ℚ} {options : LinearSys.AdaptiveOptions 𝕋} {s s' : LinearSys.AdaptiveState 𝕋 n}
    {r : LinearSys.AdaptiveStepInfo 𝕋 n}
    (h : sys.adaptiveStepFloat X₀ V t₀ tf options s = some (r, s'))
    (hinv : sys.AdaptiveInvariant V s) :
    sys.AdaptiveInvariant V s' ∧ s.t < s'.t ∧ r.tStart = t₀ + s.t ∧
      r.tEnd = t₀ + min s'.t tf ∧
      ∀ {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := 𝒮) (Set.Icc 0 (tf : ℝ)) X₀.construct U x u →
        U ⊆ V.construct → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ tf →
          x t ∈ r.R.construct := by -- --- PROOF ---
  obtain ⟨h0, hlo, hhi, hP⟩ := hinv
  unfold LinearSys.adaptiveStepFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sq, hsq, ⟨Δt, η, εH, εP⟩, -, h⟩ := h
  dsimp only at h
  split_ifs at h with hcheck
  obtain ⟨hΔ, hη2, hnrm, -, -⟩ := hcheck
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set A := Scalar.toRealMat sys.A with hA
  set eAt := sys.expSquaringFloat s.tLo s.tHi (max options.ηmax 2) sq with heAt
  set ũ := Recentre.centre V with hũ
  set Ũ := Recentre.recentre V with hŨ
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  set ti : ℝ := (s.t : ℝ) with hti
  have hti0 : 0 ≤ ti := by rw [hti]; exact_mod_cast h0
  have hΔr : 0 < toReal Δt := by rw [← ToRat.toReal_toRat]; exact_mod_cast hΔ
  -- the order the check admitted, read back from ℚ
  have hadm : sys.OrderAdmissibleFloat Δt Δt η := ⟨hη2, by
    have h := (Rat.cast_le (K := ℝ)).mpr hnrm
    push_cast at h
    rwa [← ToRat.toReal_toRat]⟩
  -- `[e^{At_i}] Z` holds `e^{At_i} z`
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (ti • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAt Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAt Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec (le_max_right _ _) hsq) hlo hhi) (Set.mem_image_of_mem _ hz))
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
  have hPu := sys.inputReach_subset_inputSolutionFloat hΔr hadm _ (hconst hpt hΔr.le)
  have hPU := sys.inputReach_subset_inputSolutionFloat hΔr hadm Ũ
  -- the `Ũ`-input's share by `t_i + Δt` comes apart at `t_i`
  have hsep : ∀ y ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ (toReal Δt + ti),
      ∃ p ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ (toReal Δt),
        ∃ q ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ ti, y = exp (ti • A)
          *ᵥ p + q := by
    intro y hy
    obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩ := sys.inputReach_separation_subset hΔr.le
      hti0 (CompactSet.isBounded_construct Ũ) hy
    exact ⟨p, hp, q, hq, rfl⟩
  -- the constant's share comes apart the same way
  have hΓ : ∀ {τ : ℝ}, 0 ≤ τ → Real.MatExp.expIntegral A (τ + ti) *ᵥ ũ
      = exp (ti • A) *ᵥ (Real.MatExp.expIntegral A τ *ᵥ ũ) + Real.MatExp.expIntegral A ti *ᵥ ũ :=
    fun hτ => Real.MatExp.expIntegral_add_mulVec A ũ hτ hti0
  have ht' : (((s.t + ToRat.toRat Δt : ℚ)) : ℝ) = toReal Δt + ti := by
    push_cast; rw [ToRat.toReal_toRat]; ring
  refine ⟨?_, by linarith, rfl, rfl, ?_⟩
  · -- the next state: later, still bracketed, and its `P` one step on
    refine ⟨by have := hΔ.le; linarith, ?_, ?_, ?_⟩
    · rw [ht']; exact (addDown_le_add _ _).trans (by linarith)
    · rw [ht']; exact le_trans (by linarith) (add_le_addUp _ _)
    · intro y hy
      rw [ht'] at hy ⊢
      obtain ⟨p, hp, q, hq, rfl⟩ := hsep y hy
      -- `Γ(t_i) ũ + q` is in `P(t_i)`, the rest is `[e^{At_i}]` of this step's share
      dsimp only
      refine Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _ ?_
      refine Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ ?_
      rw [hΓ hΔr.le, show exp (ti • A) *ᵥ (Real.MatExp.expIntegral A (toReal Δt) *ᵥ ũ)
          + Real.MatExp.expIntegral A ti *ᵥ ũ + (exp (ti • A) *ᵥ p + q)
          = (Real.MatExp.expIntegral A ti *ᵥ ũ + q)
            + exp (ti • A) *ᵥ (Real.MatExp.expIntegral A (toReal Δt) *ᵥ ũ + p) by
        rw [Matrix.mulVec_add]; abel]
      exact Set.add_mem_add (hP q hq)
        (hmt (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hPu (hPU hp))))
  · intro U x u traj hUV t ht htf
    rw [ht'] at ht
    have ht0 : 0 ≤ t := hti0.trans ht.1
    set τ := t - ti with hτ
    have hτ0 : 0 ≤ τ := sub_nonneg.mpr ht.1
    have hτΔ : τ ≤ toReal Δt := by linarith [ht.2]
    -- the run's departure from the free motion and the constant's share, by `t_{i+1}`
    have hd := traj.sub_mem_inputReach_recentre (S' := 𝒵[𝕋]) (V := V)
      hUV ⟨ht0, htf⟩
    have hd' := sys.inputReach_mono (S := 𝒵[𝕋])
      (CompactSet.isBounded_construct Ũ)
      (Recentre.zero_mem_recentre V) ht0 ht.2 hd
    obtain ⟨p, hp, q, hq, hpq⟩ := hsep _ hd'
    -- the free motion and the constant over `[0, τ]`, inside `HR₀ ⊕ P̃^R`
    have hc := sys.inputReach_subset_inputSolutionFloat hΔr hadm seg
      (sys.inputReach_mono (S := 𝒵[𝕋])
        (CompactSet.isBounded_construct seg) h0seg hτ0 hτΔ
        (hconst hũseg hτ0))
    have hcore := Plus.plus_outer (sys.timeIntervalStepFloat Δt η X₀)
      (sys.inputSolutionFloat Δt η seg) (Set.add_mem_add
        (sys.timeIntervalStepFloat_outer hΔr hadm X₀ traj.init hτ0 hτΔ) hc)
    -- `e^{At}` splits at `t_i`, so `x t` regroups as the window's summands
    have hexp : exp (t • A) = exp (ti • A) * exp (τ • A) := by
      rw [show t = ti + τ by ring, add_smul]
      exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
    have hx : x t = exp (ti • A) *ᵥ ((exp (τ • A) *ᵥ x 0 + Real.MatExp.expIntegral A τ *ᵥ ũ) + p)
        + (Real.MatExp.expIntegral A ti *ᵥ ũ + q) := by
      have hsplit : x t = (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)
          + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)) := by abel
      rw [hsplit, hpq, hexp, ← Matrix.mulVec_mulVec, show t = τ + ti by ring, hΓ hτ0,
        Matrix.mulVec_add, Matrix.mulVec_add]
      abel
    rw [hx]
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (hmt (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add hcore (hPU hp)))) (hP q hq))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
