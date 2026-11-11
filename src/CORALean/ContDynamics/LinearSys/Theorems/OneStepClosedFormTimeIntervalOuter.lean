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
# `oneStepClosedForm` holds the state at every time of the step

`Rti` of `LinearSys.oneStepClosedForm` encloses `x(t)` for every `t ∈ [0, Δt]` of every run from `X`
whose input is the constant `u` plus a signal in `U ∋ 0`: the proof of `oneStep_timeInterval_outer`
with `F`, `G` and the remainder of `PU`, `Pu` entrywise, as in CORA [1], so nothing is
asked of the Taylor order. The state is the interpolated point of the hull, `F x₀`, `G u` and the
input's share. Outer only: the hull is a `linComb`, and `Pu`, `PU`, `F`, `G` are bounds.

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
* `t` – time

## Hypotheses
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `h0` – origin lies in the input set
* `ht0` – time nonnegative
* `htΔ` – time within the step
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
* the state at the time lies in the time-interval set

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

/-- The state at every time of the step is in `oneStepClosedForm`'s time-interval set. -/
theorem LinearSys.IsCanonicalTrajectory.oneStepClosedForm_timeInterval_outer {sys : LinearSys 𝕋 n}
    {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    {X U W P : S n}
    {x w : ℝ → Vec ℝ n} {u : Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (Set.Icc 0 Δt) X W x w) (h0 : (0 : Vec ℝ n) ∈ toSet U)
    {t : ℝ} (ht0 : 0 ≤ t) (htΔ : t ≤ Δt)
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
    x t ∈ toSet (sys.oneStepClosedForm X U u Δt (m + 2)).Rti := by -- --- PROOF ---
  subst hP
  set A := toRealMat sys.A with hA
  set lam : ℝ := t / Δt with hlam
  have hl0 : 0 ≤ lam := div_nonneg ht0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr htΔ
  have hp := traj.sub_mem_inputReach_shift u hWU hW hbdd ⟨ht0, htΔ⟩
  have hPU := sys.inputReach_subset_inputSolutionEntrywise hΔt (m + 2) hconv hclosed hbdd hRconv
    hRclosed hRbdd (sys.inputReach_mono hbdd h0 ht0 htΔ hp)
  have hPu := sys.inputReach_subset_inputSolutionEntrywise (U := (OfPoint.ofPoint u : S n)) hΔt
    (m + 2) pconv pclosed pbdd pRconv pRclosed pRbdd
    ⟨fun _ => u, fun _ _ => OfPoint.mem_ofPoint u, aestronglyMeasurable_const,
      (MatExp.expIntegral_constInput A u hΔt.le).symm⟩
  have hex : exp (Δt • A) *ᵥ x 0 ∈ toSet (Mtimes.mtimes (exp (Δt • A)) X) :=
    Mtimes.mtimes_outer _ X (Set.mem_iUnion₂.mpr ⟨_, rfl, Set.mem_image_of_mem _ traj.init⟩)
  -- the hull of `X` and `Htp` holds the interpolated point
  have hHtp : exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u
      ∈ toSet (Plus.plus (Mtimes.mtimes (exp (Δt • A)) X)
        (sys.inputSolutionEntrywise Δt (m + 2) (OfPoint.ofPoint u : S n))) :=
    Plus.plus_outer _ _ (Set.add_mem_add hex hPu)
  have hlin := LinComb.linComb_outer X (Plus.plus (Mtimes.mtimes (exp (Δt • A)) X)
    (sys.inputSolutionEntrywise Δt (m + 2) (OfPoint.ofPoint u : S n)))
    ⟨x 0, traj.init, _, hHtp, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- the two interpolation errors
  have hF : (exp (t • A) - 1 - lam • (exp (Δt • A) - 1)) *ᵥ x 0
      ∈ toSet (Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrixEntrywise A Δt (m + 2)) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ) _ X (Set.mem_biUnion
      (MatExp.expDiff_mem_correctionMatrixEntrywise A hΔt ht0 htΔ)
      (Set.mem_image_of_mem _ traj.init))
  have hG : (MatExp.expIntegral A t - lam • MatExp.expIntegral A Δt) *ᵥ u
      ∈ toSet (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrixEntrywise A Δt (m + 2))
        (OfPoint.ofPoint (S := S n) u)) :=
    Mtimes.mtimes_outer (𝕄 := ℐ) _ _ (Set.mem_biUnion
      (MatExp.expIntegralDiff_mem_constCorrectionMatrixEntrywise A hΔt (m + 2) ht0 htΔ)
      (Set.mem_image_of_mem _ (OfPoint.mem_ofPoint u)))
  -- the state is the interpolated point, the two errors, and the input's share
  have hx : x t = ((((1 - lam) • x 0 + lam • (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u))
      + (exp (t • A) - 1 - lam • (exp (Δt • A) - 1)) *ᵥ x 0)
      + (x t - (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ u)))
      + (MatExp.expIntegral A t - lam • MatExp.expIntegral A Δt) *ᵥ u := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul,
      smul_add]
    abel
  -- the four parts, regrouped into `((Hti ⊞ PU) ⊞ C_input)`
  show x t ∈ toSet (Plus.plus (Plus.plus _ _) _)
  rw [hx]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add hlin hF)) hPU)) hG)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
