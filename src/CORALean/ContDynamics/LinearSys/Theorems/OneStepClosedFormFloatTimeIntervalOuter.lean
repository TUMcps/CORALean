module

public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedFormFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatLeEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ToSetPoint

@[expose] public section

/-!
# `oneStepClosedFormFloat` holds the state at every time of the step

`oneStepClosedForm_timeInterval_outer` [1] at the float sets: the state at `t` is the point of the
hull of `X` and `Htp` at `t/Δt`, plus the two interpolation errors, which `[F] X` and `[G] u` hold
at the remainder bound the step computed, plus the `U`-input's share in `PU`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `u` – float constant input
* `η` – Taylor order
* `X` – start float zonotope
* `U` – input float zonotope
* `W` – set of trajectory inputs
* `x` – state trajectory
* `w` – input signal
* `t` – time in the step

## Hypotheses
* `hη` – Taylor order at least two
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `h0` – input set holds the origin
* `ht0` – time nonnegative
* `htΔ` – time within the step
* `hWU` – shifted inputs lie in the input set
* `hW` – set of trajectory inputs bounded

## Conclusion
* the state at the time lies in the time-interval set

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix Pointwise ContSet ContSetLike NormedSpace
open MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at every time of the step is in `oneStepClosedFormFloat`'s time-interval set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStepClosedFormFloat_timeInterval_outer
    {sys : LinearSys 𝕋 n} {Δt : 𝕋} {u : Vec 𝕋 n}
    {η : ℕ} (hη : 2 ≤ η) (hΔt : 0 < toReal Δt) {X U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) X.toSet
      W x w)
    (h0 : (0 : Vec ℝ n) ∈ U.toSet) {t : ℝ} (ht0 : 0 ≤ t) (htΔ : t ≤ toReal Δt)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.toSet) (hW : Bornology.IsBounded W) : -- --- CONCL ---
    ∀ R ∈ sys.oneStepClosedFormFloat X U u Δt η, x t ∈ R.Rti.toSet := by -- --- PROOF ---
  intro R h
  rw [Option.mem_def] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set uR := toRealVec u with huR
  set lam : ℝ := t / r with hlam
  have hl0 : 0 ≤ lam := div_nonneg ht0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr htΔ
  -- the order the step enclosed the exponential at, and the remainder bound it computed
  unfold LinearSys.oneStepClosedFormFloat at h
  dsimp only at h
  cases hop : MatExp.admissibleOrder (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point (Interval.magnitudeMat (Interval.point sys.A)))))
      (m + 2) MatExp.expEnclosureFuel with
  | none => rw [hop] at h; exact absurd h (by simp)
  | some ηe =>
  rw [hop] at h
  have hε := (MatExp.admissibleOrder_spec ηe hop).1
  have hWle := fun j k => MatExp.expRemainderMat_le_expRemainderEntrywise sys.A (m + 2) ηe hε j k
  simp only [Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at h
  subst h
  -- the `U`-input's share up to `t`, lifted to `Δt`, in `PU`
  have hU := CompactSet.isBounded_toSet U
  have hp := traj.sub_mem_inputReach_shift (S := ExactSet) (U := U.toSet) uR hWU hW hU
    ⟨ht0, htΔ⟩
  have hPU := sys.inputReach_subset_inputSolutionEntrywiseFloat hΔt _ hWle U
    (sys.inputReach_mono (S := 𝒵[𝕋]) hU h0 ht0 htΔ hp)
  -- the constant's share, in `Pu`
  have hpt : uR ∈ (Zonotope.point u).toSet := by
    rw [Zonotope.toSet_point]; exact rfl
  have hPu := sys.inputReach_subset_inputSolutionEntrywiseFloat hΔt _ hWle (Zonotope.point u)
    ⟨fun _ => uR, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A uR hΔt.le).symm⟩
  -- the free motion, in `[e^{AΔt}] X`
  have hex : exp (r • A) *ᵥ x 0 ∈ toSet (Mtimes.mtimes (ContSet := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) (sys.expEntrywiseFloat Δt (m + 2) _) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (sys.exp_mem_expEntrywiseFloat (m + 2) _ hΔt.le hWle)
        (Set.mem_image_of_mem _ traj.init))
  -- the `linComb` of `X` and `Htp` holds the interpolated point
  have hHtp : exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR
      ∈ toSet (Plus.plus (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (sys.expEntrywiseFloat Δt (m + 2) _) X)
        (sys.inputSolutionEntrywiseFloat Δt (m + 2) _ (Zonotope.point u))) :=
    Plus.plus_outer _ _ (Set.add_mem_add hex hPu)
  have hlin := LinComb.linComb_outer X (Plus.plus (Mtimes.mtimes (ContSet := 𝒵[𝕋])
    (𝕄 := ℐ[𝕋]) (sys.expEntrywiseFloat Δt (m + 2) _) X)
    (sys.inputSolutionEntrywiseFloat Δt (m + 2) _ (Zonotope.point u)))
    ⟨x 0, traj.init, _, hHtp, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- the two interpolation errors
  have hF : (exp (t • A) - 1 - lam • (exp (r • A) - 1)) *ᵥ x 0
      ∈ toSet (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalCorrectionMatrixEntrywise (Interval.point sys.A) Δt (m + 2) _) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (MatExp.expDiff_mem_intervalCorrectionMatrixEntrywise _ hΔt _
        (Interval.mem_point sys.A) hWle ht0 htΔ) (Set.mem_image_of_mem _ traj.init))
  have hG : (Real.MatExp.expIntegral A t - lam • Real.MatExp.expIntegral A r) *ᵥ uR
      ∈ toSet (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalConstCorrectionMatrixEntrywise (Interval.point sys.A) Δt (m + 2) _)
        (Zonotope.point u)) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) _ _
      (Set.mem_biUnion (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrixEntrywise _ hΔt
        (m + 2) _ (Interval.mem_point sys.A) hWle ht0 htΔ) (Set.mem_image_of_mem _ hpt))
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
  show x t ∈ (Plus.plus (Plus.plus _ _) _ : Zonotope (Vec 𝕋 n)).toSet
  rw [hx]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hlin hF)) hPU)) hG)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
