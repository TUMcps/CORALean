module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.OneStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

@[expose] public section

/-!
# `oneStepFloat` holds the state at every time of the step

`oneStep_timeInterval_outer` [1, Sec. 3.3] at the float sets: with `λ = t/Δt`, the state
`x(t)` of a run from `X` whose input is the constant `u` plus a signal in `U ∋ 0` is
`(1-λ) x₀ + λ (e^{AΔt} x₀ + Γ(Δt) u)`, a point of the `linComb` of `X` and `Htp`, plus the state's
interpolation error, in `[F] X` (`expDiff_mem_intervalCorrectionMatrix`), the constant's, in
`[G] {u}` (`expIntegralDiff_mem_intervalConstCorrectionMatrix`), and a `U`-input's contribution
up to `t`, which `0 ∈ U` lifts to `Δt` (`inputReach_mono`) and `PU` holds
(`inputReach_subset_inputSolutionFloat`).

The real theorem's convexity, closedness and boundedness hypotheses are gone, as in
`oneStepFloat_timePoint_outer`; `0 ∈ U` stays. Outer only.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix Pointwise ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at every time of the step is in `oneStepFloat`'s time-interval set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStepFloat_timeInterval_outer {sys : LinearSys 𝕋 n}
    {Δt : 𝕋}
    {η : ℕ} (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) {X U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n} {u : Vec 𝕋 n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 (toReal Δt)) X.construct
      W x w)
    (h0 : (0 : Vec ℝ n) ∈ U.construct) {t : ℝ} (ht0 : 0 ≤ t) (htΔ : t ≤ toReal Δt)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.construct) (hW : Bornology.IsBounded W) : -- --- STMT ---
    x t ∈ (sys.oneStepFloat X U u Δt η).Rti.construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set uR := toRealVec u with huR
  set lam : ℝ := t / r with hlam
  have hl0 : 0 ≤ lam := div_nonneg ht0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr htΔ
  -- the `U`-input's share up to `t`, lifted to `Δt`, in `PU`
  have hU := CompactSet.isBounded_construct U
  have hp := traj.sub_mem_inputReach_shift (S := 𝒮) (U := U.construct) uR
    hWU hW hU ⟨ht0, htΔ⟩
  have hPU := sys.inputReach_subset_inputSolutionFloat hΔt hη U
    (sys.inputReach_mono (S := 𝒵[𝕋]) hU h0 ht0 htΔ hp)
  -- the constant's share, in `Pu`
  have hpt : uR ∈ (Zonotope.point u).construct := by
    rw [Zonotope.construct_point]; exact rfl
  have hPu := sys.inputReach_subset_inputSolutionFloat hΔt hη (Zonotope.point u)
    ⟨fun _ => uR, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A uR hΔt.le).symm⟩
  -- the free motion, in `[e^{AΔt}] X`
  have hex : exp (r • A) *ᵥ x 0 ∈ construct (Mtimes.mtimes (S := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) (sys.expIntervalFloat Δt Δt (m + 2)) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl)
        (Set.mem_image_of_mem _ traj.init))
  -- the `linComb` of `X` and `Htp` holds the interpolated point
  have hHtp : exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR
      ∈ construct (Plus.plus (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (sys.expIntervalFloat Δt Δt (m + 2)) X)
        (sys.inputSolutionFloat Δt (m + 2) (Zonotope.point u))) :=
    Plus.plus_outer _ _ (Set.add_mem_add hex hPu)
  have hlin := LinComb.linComb_outer X (Plus.plus (Mtimes.mtimes (S := 𝒵[𝕋])
    (𝕄 := ℐ[𝕋]) (sys.expIntervalFloat Δt Δt (m + 2)) X)
    (sys.inputSolutionFloat Δt (m + 2) (Zonotope.point u)))
    ⟨x 0, traj.init, _, hHtp, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- the two interpolation errors
  have hF : (exp (t • A) - 1 - lam • (exp (r • A) - 1)) *ᵥ x 0
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt (m + 2)) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (MatExp.expDiff_mem_intervalCorrectionMatrix _ hΔt hη.2
        (Interval.mem_point sys.A) ht0 htΔ) (Set.mem_image_of_mem _ traj.init))
  have hG : (Real.MatExp.expIntegral A t - lam • Real.MatExp.expIntegral A r) *ᵥ uR
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalConstCorrectionMatrix (Interval.point sys.A) Δt (m + 2))
        (Zonotope.point u)) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ _
      (Set.mem_biUnion (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix _ hΔt (m + 2)
        hη.2 (Interval.mem_point sys.A) ht0 htΔ) (Set.mem_image_of_mem _ hpt))
  -- the state is the interpolated point, the two errors, and the input's share
  have hx : x t = ((((1 - lam) • x 0 + lam • (exp (r • A) *ᵥ x 0
        + Real.MatExp.expIntegral A r *ᵥ uR))
      + (exp (t • A) - 1 - lam • (exp (r • A) - 1)) *ᵥ x 0)
      + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ uR)))
      + (Real.MatExp.expIntegral A t - lam • Real.MatExp.expIntegral A r) *ᵥ uR := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul,
      smul_add]
    abel
  -- the four parts, regrouped into `((Hti ⊞ PU) ⊞ C_input)`
  rw [hx]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hlin hF)) hPU)) hG)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
