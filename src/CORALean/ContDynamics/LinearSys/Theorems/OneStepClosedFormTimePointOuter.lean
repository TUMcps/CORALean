module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedForm
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionEntrywise
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift

@[expose] public section

/-!
# `oneStepClosedForm` holds the state at the end of the step

`Rtp` of `LinearSys.oneStepClosedForm` encloses `x(Δt)` of every run from `X` whose input is the
constant `u` plus a signal in `U`: the proof of `oneStep_timePoint_outer` with the entrywise
remainder `E(Δt,η)` of [1] in `PU` and `Pu`, so nothing is asked of the Taylor order.
The hypotheses on `U` and on `{u}` are the ones `inputReach_subset_inputSolutionEntrywise` takes of
the set it is applied at. Outer only: neither `Pu` nor `PU` is exact.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `m` – Taylor order offset
* `X` – start set
* `U` – input set
* `W` – set of trajectory inputs
* `P` – set of the constant input
* `x` – state trajectory
* `w` – input signal
* `u` – constant input

## Hypotheses
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `hWU` – shifted inputs lie in the input set
* `hW` – set of trajectory inputs bounded
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image of the input set convex
* `hRclosed` – remainder image of the input set closed
* `hRbdd` – remainder image of the input set bounded
* `hP` – the constant input's set is the point `{u}`
* `pconv` – constant input point convex
* `pclosed` – constant input point closed
* `pbdd` – constant input point bounded
* `pRconv` – remainder image of the constant input convex
* `pRclosed` – remainder image of the constant input closed
* `pRbdd` – remainder image of the constant input bounded

## Conclusion
* the state at the end of the step lies in the time-point set

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet ContSetLike Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at the end of the step is in `oneStepClosedForm`'s time-point set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStepClosedForm_timePoint_outer {sys : LinearSys 𝕋 n}
    {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    {X U W P : S n}
    {x w : ℝ → Vec ℝ n} {u : Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (Set.Icc 0 Δt) X W x w)
    (hWU : ∀ v ∈ toSet W, v - u ∈ toSet U) (hW : Bornology.IsBounded (toSet W))
    (hconv : Convex ℝ (toSet U)) (hclosed : IsClosed (toSet U))
    (hbdd : Bornology.IsBounded (toSet U))
    (hRconv : Convex ℝ (sys.inputRemainderEntrywiseSet Δt (m + 2) U))
    (hRclosed : IsClosed (sys.inputRemainderEntrywiseSet Δt (m + 2) U))
    (hRbdd : Bornology.IsBounded (sys.inputRemainderEntrywiseSet Δt (m + 2) U))
    (hP : P = OfPoint.ofPoint u) (pconv : Convex ℝ (toSet P))
    (pclosed : IsClosed (toSet P))
    (pbdd : Bornology.IsBounded (toSet P))
    (pRconv : Convex ℝ (sys.inputRemainderEntrywiseSet Δt (m + 2) P))
    (pRclosed : IsClosed (sys.inputRemainderEntrywiseSet Δt (m + 2) P))
    (pRbdd : Bornology.IsBounded (sys.inputRemainderEntrywiseSet Δt (m + 2) P))
    : -- --- CONCL ---
    x Δt ∈ toSet (sys.oneStepClosedForm X U u Δt (m + 2)).Rtp := by -- --- PROOF ---
  subst hP
  set A := toRealMat sys.A with hA
  have hU := hbdd
  have hp := traj.sub_mem_inputReach_shift u hWU hW hU ⟨hΔt.le, le_rfl⟩
  have hPU := sys.inputReach_subset_inputSolutionEntrywise hΔt (m + 2) hconv hclosed hbdd hRconv
    hRclosed hRbdd hp
  have hPu := sys.inputReach_subset_inputSolutionEntrywise (U := (OfPoint.ofPoint u : S n)) hΔt
    (m + 2) pconv pclosed pbdd pRconv pRclosed pRbdd
    ⟨fun _ => u, fun _ _ => OfPoint.mem_ofPoint u, aestronglyMeasurable_const,
      (MatExp.expIntegral_constInput A u hΔt.le).symm⟩
  have hex : exp (Δt • A) *ᵥ x 0 ∈ toSet (Mtimes.mtimes (exp (Δt • A)) X) :=
    Mtimes.mtimes_outer _ X (Set.mem_iUnion₂.mpr ⟨_, rfl, Set.mem_image_of_mem _ traj.init⟩)
  have hx : x Δt = (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u)
      + (x Δt - (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u)) := by abel
  show x Δt ∈ toSet (Plus.plus _ _)
  rw [hx]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add hex hPu)) hPU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
