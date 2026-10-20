module

public import CORALean.ContDynamics.LinearSys.Operations.OneStep
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift

@[expose] public section

/-!
# `oneStep` holds the state at the end of the step

`Rtp` of `LinearSys.oneStep` [1, Sec. 3.3] encloses `x(Δt)` of every run from `X` whose input is the
constant `u` plus a signal in `U`: the state is `e^{AΔt} x₀ + Γ(Δt) u + p` with `p` one
`U`-input's contribution (`sub_mem_inputReach_shift`), the first two summands lie in
`Htp = e^{AΔt} X ⊕ Pu` by `Pu`'s own soundness at the constant input, and `p` in `PU`.

The hypotheses on `U` and on `{u}` are the ones `inputReach_subset_inputSolution` takes of the
set it is applied at. Outer only: neither `Pu` nor `PU` is exact.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `m` – Taylor order offset
* `X` – start set
* `U` – input set
* `W` – set of trajectory inputs
* `x` – state trajectory
* `w` – input signal
* `u` – constant input

## Hypotheses
* `hΔt` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `traj` – signal is a canonical trajectory
* `hWU` – shifted inputs lie in the input set
* `hW` – set of trajectory inputs bounded
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image of the input set convex
* `hRclosed` – remainder image of the input set closed
* `hRbdd` – remainder image of the input set bounded
* `pconv` – constant input point convex
* `pclosed` – constant input point closed
* `pbdd` – constant input point bounded
* `pRconv` – remainder image of the constant input convex
* `pRclosed` – remainder image of the constant input closed
* `pRbdd` – remainder image of the constant input bounded

## Conclusion
* the state at the end of the step lies in the time-point set

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at the end of the step is in `oneStep`'s time-point set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStep_timePoint_outer {sys : LinearSys 𝕋 n} {Δt : ℝ}
    (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {X U W : S n}
    {x w : ℝ → Vec ℝ n} {u : Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (Set.Icc 0 Δt) X W x w)
    (hWU : ∀ v ∈ construct W, v - u ∈ construct U) (hW : Bornology.IsBounded (construct W))
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (pconv : Convex ℝ (construct (OfPoint.ofPoint (S := S n) u)))
    (pclosed : IsClosed (construct (OfPoint.ofPoint (S := S n) u)))
    (pbdd : Bornology.IsBounded (construct (OfPoint.ofPoint (S := S n) u)))
    (pRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u))))
    (pRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u))))
    (pRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u))))
    : -- --- CONCL ---
    x Δt ∈ construct (sys.oneStep X U u Δt (m + 2)).Rtp := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  have hU := hbdd
  have hp := traj.sub_mem_inputReach_shift u hWU hW hU ⟨hΔt.le, le_rfl⟩
  have hPU := sys.inputReach_subset_inputSolution hΔt (m + 2) hε hconv hclosed hbdd hRconv
    hRclosed hRbdd hp
  have hPu := sys.inputReach_subset_inputSolution (U := (OfPoint.ofPoint u : S n)) hΔt (m + 2)
    hε pconv pclosed pbdd pRconv pRclosed pRbdd
    ⟨fun _ => u, fun _ _ => OfPoint.mem_ofPoint u, aestronglyMeasurable_const,
      (MatExp.expIntegral_constInput A u hΔt.le).symm⟩
  have hex : exp (Δt • A) *ᵥ x 0 ∈ construct (Mtimes.mtimes (exp (Δt • A)) X) :=
    Mtimes.mtimes_outer _ X (Set.mem_iUnion₂.mpr ⟨_, rfl, Set.mem_image_of_mem _ traj.init⟩)
  have hx : x Δt = (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u)
      + (x Δt - (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u)) := by abel
  show x Δt ∈ construct (Plus.plus _ _)
  rw [hx]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add hex hPu)) hPU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
