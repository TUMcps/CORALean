module

public import CORALean.ContDynamics.LinearSys.Operations.OneStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachShift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

@[expose] public section

/-!
# `oneStepFloat` holds the state at the end of the step

`oneStep_timePoint_outer` [1, Sec. 3.3] at the float sets: `x(Δt)` of every run from `X` whose input
is the constant `u` plus a signal in `U` is `e^{AΔt} x₀ + Γ(Δt) u + p` with `p` one `U`-input's
contribution (`sub_mem_inputReach_shift`). `e^{AΔt}` is in `expIntervalFloat`
(`exp_mem_expIntervalFloat`), `Γ(Δt) u` is the constant input's contribution, which `Pu` holds, and
`p` is in `PU`, both by `inputReach_subset_inputSolutionFloat`.

The real theorem's convexity, closedness and boundedness hypotheses on `U`, `{u}` and their
remainder images are gone: float zonotopes have all three, and the float input solution's
soundness asks only an admissible order. Outer only.

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

/-- The state at the end of the step is in `oneStepFloat`'s time-point set. -/
theorem LinearSys.CanonicalTrajectory.oneStepFloat_timePoint_outer {sys : LinearSys 𝕋 n} {Δt : 𝕋}
    {η : ℕ} (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) {X U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n} {u : Vec 𝕋 n}
    (traj : sys.CanonicalTrajectory (S := 𝒮) (Set.Icc 0 (toReal Δt)) X.construct
      W x w)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.construct) (hW : Bornology.IsBounded W) :
    x (toReal Δt) ∈ (sys.oneStepFloat X U u Δt η).Rtp.construct := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  -- the `U`-input's share, in `PU`
  have hp := traj.sub_mem_inputReach_shift (S := 𝒮) (U := U.construct)
    (toRealVec u) hWU hW (CompactSet.isBounded_construct U) ⟨hΔt.le, le_rfl⟩
  have hPU := sys.inputReach_subset_inputSolutionFloat hΔt hη U hp
  -- the constant's share, in `Pu`
  have hpt : toRealVec u ∈ (Zonotope.point u).construct := by
    rw [Zonotope.construct_point]; exact rfl
  have hPu := sys.inputReach_subset_inputSolutionFloat hΔt hη (Zonotope.point u)
    ⟨fun _ => toRealVec u, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A (toRealVec u) hΔt.le).symm⟩
  -- the free motion, in `[e^{AΔt}] X`
  have hex : exp (r • A) *ᵥ x 0 ∈ construct (Mtimes.mtimes (S := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) (sys.expIntervalFloat Δt Δt η) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ X
      (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl)
        (Set.mem_image_of_mem _ traj.init))
  have hx : x r = (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ toRealVec u)
      + (x r - (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ toRealVec u)) := by abel
  rw [hx]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hex hPu)) hPU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
