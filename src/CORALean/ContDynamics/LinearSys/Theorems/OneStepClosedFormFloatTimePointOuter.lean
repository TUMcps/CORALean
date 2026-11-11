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
# `oneStepClosedFormFloat` holds the state at the end of the step

`oneStepClosedForm_timePoint_outer` [1] at the float sets: `x(Δt)` is `e^{AΔt} x₀ + Γ(Δt) u + p`,
with `e^{AΔt}` in `expEntrywiseFloat`, `Γ(Δt) u` in `Pu` and `p` in `PU`, both by
`inputReach_subset_inputSolutionEntrywiseFloat`. The remainder bound `W` the step computes holds
`E(Δt,η)` for the order `admissibleOrder` found, by `expRemainderMat_le_expRemainderEntrywise`. No
condition is asked of `η`: the step computes its own enclosure or returns `none`.

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

## Hypotheses
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `hWU` – shifted inputs lie in the input set
* `hW` – set of trajectory inputs bounded

## Conclusion
* the state at the end of the step lies in the time-point set

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

/-- The state at the end of the step is in `oneStepClosedFormFloat`'s time-point set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStepClosedFormFloat_timePoint_outer
    {sys : LinearSys 𝕋 n} {Δt : 𝕋} {u : Vec 𝕋 n}
    {η : ℕ} (hΔt : 0 < toReal Δt) {X U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) X.toSet
      W x w)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.toSet) (hW : Bornology.IsBounded W) : -- --- CONCL ---
    ∀ R ∈ sys.oneStepClosedFormFloat X U u Δt η,
      x (toReal Δt) ∈ R.Rtp.toSet := by -- --- PROOF ---
  intro R h
  rw [Option.mem_def] at h
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set uR := toRealVec u with huR
  -- the order the step enclosed the exponential at, and the remainder bound it computed
  unfold LinearSys.oneStepClosedFormFloat at h
  dsimp only at h
  cases hop : MatExp.admissibleOrder (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point (Interval.magnitudeMat (Interval.point sys.A)))))
      η MatExp.expEnclosureFuel with
  | none => rw [hop] at h; exact absurd h (by simp)
  | some ηe =>
  rw [hop] at h
  have hε := (MatExp.admissibleOrder_spec ηe hop).1
  have hWle := fun j k => MatExp.expRemainderMat_le_expRemainderEntrywise sys.A η ηe hε j k
  simp only [Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at h
  subst h
  -- the `U`-input's share, in `PU`
  have hU := CompactSet.isBounded_toSet U
  have hpPU := traj.sub_mem_inputReach_shift (S := ExactSet) (U := U.toSet) uR hWU hW hU
    ⟨hΔt.le, le_rfl⟩
  -- the constant's share, in `Pu`
  have hpt : uR ∈ (Zonotope.point u).toSet := by
    rw [Zonotope.toSet_point]; exact rfl
  have hPu := sys.inputReach_subset_inputSolutionEntrywiseFloat hΔt _ hWle (Zonotope.point u)
    ⟨fun _ => uR, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A uR hΔt.le).symm⟩
  -- the free motion, in `[e^{AΔt}] X`
  have hex : exp (r • A) *ᵥ x 0 ∈ toSet (Mtimes.mtimes (ContSet := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) (sys.expEntrywiseFloat Δt η _) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (sys.exp_mem_expEntrywiseFloat η _ hΔt.le hWle)
        (Set.mem_image_of_mem _ traj.init))
  have hPU := sys.inputReach_subset_inputSolutionEntrywiseFloat hΔt _ hWle U hpPU
  -- the state is the free motion, the constant's share and the `U`-input's share
  have hx : x r = (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR)
      + (x r - (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR)) := by abel
  show x r ∈ (Plus.plus _ _ : Zonotope (Vec 𝕋 n)).toSet
  rw [hx]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hex hPu)) hPU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
