module

public import CORALean.ContDynamics.LinearSys.Operations.PolyOneStepClosedFormFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormMatricesFloatSpec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatLeEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ToSetPoint

@[expose] public section

/-!
# `polyOneStepClosedFormFloat` holds the state at the end of the step

`oneStepClosedForm_timePoint_outer` at the polynomial sets: the state at `Δt` is the free motion
`e^{AΔt} x₀`, in `[e^{AΔt}] X` (`mtimesIntervalMat_outer`), the constant's share, in `Pu`, and the
`U`-input's share, in `PU`; the two zonotopes are added as independent generators.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `u` – float constant input
* `η` – Taylor order
* `order` – the order of equal exponent columns
* `X` – start polynomial zonotope
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
* the state at the end lies in the time-point set, for the matrices the system forms
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
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

/-- The state at the end of the step is in `polyOneStepClosedFormFloat`'s time-point set. -/
theorem LinearSys.IsCanonicalTrajectory.polyOneStepClosedFormFloat_timePoint_outer
    {sys : LinearSys 𝕋 n} {Δt : 𝕋} {u : Vec 𝕋 n}
    {η : ℕ} {order : ℕ → Array (Array ℕ) → Array ℕ} (hΔt : 0 < toReal Δt)
    {X : PolyZonotope (Vec 𝕋 n)} {U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) X.toSet
      W x w)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.toSet) (hW : Bornology.IsBounded W) : -- --- CONCL ---
    ∀ M ∈ sys.closedFormMatricesFloat Δt η,
      x (toReal Δt) ∈
        (sys.polyOneStepClosedFormFloat M X U u Δt order).Rtp.toSet := by -- --- PROOF ---
  intro M hM
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set uR := toRealVec u with huR
  -- the order the step enclosed the exponential at, and the remainder bound it computed
  obtain ⟨hop, hWM, s, hs, heA, hFM, hGM⟩ := LinearSys.closedFormMatricesFloat_spec M hM
  rcases M with ⟨ηe, W', eAdt', F', G'⟩
  dsimp only at hop hWM heA hFM hGM
  subst hWM heA
  subst hFM hGM
  have hε := (MatExp.admissibleOrder_spec ηe hop).1
  have hWle := fun j k => MatExp.expRemainderMat_le_expRemainderEntrywise sys.A ηe ηe hε j k
  -- the count of halvings, at which the squared enclosure of `e^{AΔt}` is admissible
  have hs16 := sys.halvingsFloat_spec (η := 16) (by norm_num) s (Option.mem_def.mpr hs)
  unfold LinearSys.polyOneStepClosedFormFloat
  dsimp only
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
  have hex : exp (r • A) *ᵥ x 0 ∈ (PolyZonotope.mtimesIntervalMat
      (sys.expSquaringFloat Δt Δt 16 s) X).toSet :=
    PolyZonotope.mtimesIntervalMat_outer _ X
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat hs16 le_rfl le_rfl)
        (Set.mem_image_of_mem _ traj.init))
  have hPU := sys.inputReach_subset_inputSolutionEntrywiseFloat hΔt _ hWle U hpPU
  -- the state is the free motion, the constant's share and the `U`-input's share
  have hx : x r = (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR)
      + (x r - (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR)) := by abel
  have hPu' : Real.MatExp.expIntegral A r *ᵥ uR ∈ (sys.inputSolutionEntrywiseFloat Δt ηe
      (MatExp.expRemainderEntrywise sys.A Δt ηe ηe) (Zonotope.point u)).materialise.toSet := by
    rw [Zonotope.materialise_eq]; exact hPu
  have hPU' : x r - (exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR) ∈
      (sys.inputSolutionEntrywiseFloat Δt ηe (MatExp.expRemainderEntrywise sys.A Δt ηe ηe)
        U).materialise.toSet := by
    rw [Zonotope.materialise_eq]; exact hPU
  show x r ∈ (Plus.plus _ _ : PolyZonotope (Vec 𝕋 n)).toSet
  rw [hx]
  exact Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hex
      (Zonotope.ofIndep_outer _ hPu'))) (Zonotope.ofIndep_outer _ hPU'))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
