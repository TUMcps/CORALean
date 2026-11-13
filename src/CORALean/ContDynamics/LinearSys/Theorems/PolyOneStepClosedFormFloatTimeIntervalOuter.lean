module

public import CORALean.ContDynamics.LinearSys.Operations.PolyOneStepClosedFormFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormMatricesFloatSpec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatLeEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachShift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.EncloseSharedOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ToSetPoint

@[expose] public section

/-!
# `polyOneStepClosedFormFloat` holds the state at every time of the step

`oneStepClosedForm_timeInterval_outer` [1] at the polynomial sets: the state at `t` is the point of
the enclosure of `X` and `Htp` at `t/Δt`, plus the two interpolation errors, which `[F] X` and
`[G] u` hold at the remainder bound the step computed, plus the `U`-input's share in `PU`. The
enclosure keeps the factors, so the point of `X` and the point of `Htp` it is combined with are at
one value of the factors: `x₀` at `a`, and `e^{AΔt} x₀ + ∫ e^{As} ds u` at the same `a`, by the
fibers of the products and sums (`encloseShared_comb`).

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- Adding a zonotope as independent generators leaves the exponents alone. -/
private theorem aux_plus_ofIndep_E (P : PolyZonotope (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (P.plus Z.ofIndep).E = P.E := by -- --- PROOF ---
  have key : ∀ (k : Fin P.p) (l : Fin P.h), Real.PolyZonotope.plusE P.E (Zonotope.ofIndep Z).E
      (Fin.castAdd (Zonotope.ofIndep Z).p k) (Fin.castAdd (Zonotope.ofIndep Z).h l)
      = P.E k l := fun k l => by
    unfold Real.PolyZonotope.plusE
    rw [Fin.append_left (u := fun k => Fin.append (P.E k) fun _ => (0 : ℕ)), Fin.append_left]
  funext k l
  exact key k l

/-- The same for the stored sum `⊞`. -/
private theorem aux_plusM_ofIndep_E (P : PolyZonotope (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    HEq (Plus.plus P Z.ofIndep : PolyZonotope (Vec 𝕋 n)).E P.E := by -- --- PROOF ---
  apply heq_of_eq
  funext k l
  show (P.plus Z.ofIndep).materialise.E k l = P.E k l
  refine Eq.trans ?_ (congrFun (congrFun (aux_plus_ofIndep_E P Z) k) l)
  simp [PolyZonotope.materialise]

omit [SoundFloatArithmetic 𝕋] in
/-- An interval matrix times a polynomial zonotope has its exponents. -/
private theorem aux_mtimesIntervalMat_E {m : ℕ} (IM : Interval (Mat 𝕋 m n))
    (P : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    HEq (PolyZonotope.mtimesIntervalMat IM P).E P.E := by -- --- PROOF ---
  apply heq_of_eq
  funext k l
  show ((PolyZonotope.mtimes (Interval.centerMat IM) P).plus _).materialise.E k l = P.E k l
  have := congrFun (congrFun (aux_plus_ofIndep_E (PolyZonotope.mtimes (Interval.centerMat IM) P)
    (Interval.mtimesIntervalMat (Interval.matResidual IM.inf IM.sup (Interval.centerMat IM))
      P.zonotope.interval).zonotope) k) l
  refine Eq.trans ?_ this
  simp [PolyZonotope.materialise]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at every time of the step is in `polyOneStepClosedFormFloat`'s time-interval set. -/
theorem LinearSys.IsCanonicalTrajectory.polyOneStepClosedFormFloat_timeInterval_outer
    {sys : LinearSys 𝕋 n} {Δt : 𝕋} {u : Vec 𝕋 n}
    {η : ℕ} {order : ℕ → Array (Array ℕ) → Array ℕ} (hη : 2 ≤ η) (hΔt : 0 < toReal Δt)
    {X : PolyZonotope (Vec 𝕋 n)} {U : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ n)} {x w : ℝ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) X.toSet
      W x w)
    (h0 : (0 : Vec ℝ n) ∈ U.toSet) {t : ℝ} (ht0 : 0 ≤ t) (htΔ : t ≤ toReal Δt)
    (hWU : ∀ v ∈ W, v - toRealVec u ∈ U.toSet) (hW : Bornology.IsBounded W) : -- --- CONCL ---
    ∀ M ∈ sys.closedFormMatricesFloat Δt η,
      x t ∈ (sys.polyOneStepClosedFormFloat M X U u Δt order).Rti.toSet := by -- --- PROOF ---
  intro M hM
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set uR := toRealVec u with huR
  set lam : ℝ := t / r with hlam
  have hl0 : 0 ≤ lam := div_nonneg ht0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr htΔ
  -- the order the step enclosed the exponential at, and the remainder bound it computed
  obtain ⟨hop, hWM, s, hs, heA, hFM, hGM⟩ := LinearSys.closedFormMatricesFloat_spec M hM
  rcases M with ⟨ηe, W', eAdt', F', G'⟩
  dsimp only at hop hWM heA hFM hGM
  subst hWM heA
  subst hFM hGM
  have hε := (MatExp.admissibleOrder_spec ηe hop).1
  have hη2 : 2 ≤ ηe := le_trans (by omega) (MatExp.admissibleOrder_spec ηe hop).2
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hη2
  have hWle := fun j k =>
    MatExp.expRemainderMat_le_expRemainderEntrywise sys.A (m' + 2) (m' + 2) hε j k
  -- the count of halvings, at which the squared enclosure of `e^{AΔt}` is admissible
  have hs16 := sys.halvingsFloat_spec (η := 16) (by norm_num) s (Option.mem_def.mpr hs)
  unfold LinearSys.polyOneStepClosedFormFloat
  dsimp only
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
  -- the start point, at some value `a` of the factors
  obtain ⟨a, ha, hx0⟩ := (PolyZonotope.mem_toSet_iff_fiber X (x 0)).mp traj.init
  -- the constant's share as the step stores it
  set Pu := (sys.inputSolutionEntrywiseFloat Δt (m' + 2) (MatExp.expRemainderEntrywise sys.A Δt
    (m' + 2) (m' + 2)) (Zonotope.point u)).materialise with hPuD
  -- the free motion and the constant's share, at the same `a`, in `Htp`
  have hexf : exp (r • A) *ᵥ x 0 ∈ (PolyZonotope.mtimesIntervalMat
      (sys.expSquaringFloat Δt Δt 16 s) X).fiber a :=
    PolyZonotope.mtimesIntervalMat_fiber _ X (sys.exp_mem_expSquaringFloat hs16 le_rfl le_rfl)
      ha hx0
  have hPuf := Zonotope.mem_fiber_ofIndep Pu
    (by rw [hPuD, Zonotope.materialise_eq]; exact hPu) (fun _ => 0)
  have hHtpf : exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ uR ∈ (Plus.plus
      (PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X)
      Pu.ofIndep : PolyZonotope (Vec 𝕋 n)).fiber a := by
    have h1 := PolyZonotope.plus_fiber
      (PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X)
      Pu.ofIndep (a := a) hexf hPuf
    rw [← PolyZonotope.fiber_materialise] at h1
    exact h1
  -- the enclosure of `X` and `Htp` holds the interpolated point
  have hlin := (PolyZonotope.encloseShared_outer X (Plus.plus
    (PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X)
    Pu.ofIndep : PolyZonotope (Vec 𝕋 n)) rfl rfl
    ((aux_plusM_ofIndep_E (PolyZonotope.mtimesIntervalMat
      (sys.expSquaringFloat Δt Δt 16 s) X) _).trans (aux_mtimesIntervalMat_E _ X))
    (by obtain ⟨_, _, e, he, _⟩ := hx0; exact ⟨e, he⟩)
    (by obtain ⟨_, _, e, he, _⟩ := hHtpf; exact ⟨e, he⟩)).2 ha hx0 hHtpf
    (show 1 - lam ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  rw [sub_sub_cancel] at hlin
  have hlinc := PolyZonotope.construct_outer _ order hlin
  rw [← PolyZonotope.materialise_eq (PolyZonotope.construct _ order)] at hlinc
  -- the two interpolation errors
  have hF : (exp (t • A) - 1 - lam • (exp (r • A) - 1)) *ᵥ x 0
      ∈ (PolyZonotope.mtimesIntervalMat
        (MatExp.intervalCorrectionMatrixEntrywise (Interval.point sys.A) Δt (m' + 2) _) X).toSet :=
    PolyZonotope.mtimesIntervalMat_outer _ X
      (Set.mem_biUnion (MatExp.expDiff_mem_intervalCorrectionMatrixEntrywise _ hΔt _
        (Interval.mem_point sys.A) hWle ht0 htΔ) (Set.mem_image_of_mem _ traj.init))
  have hG : (Real.MatExp.expIntegral A t - lam • Real.MatExp.expIntegral A r) *ᵥ uR
      ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalConstCorrectionMatrixEntrywise (Interval.point sys.A) Δt (m' + 2)
          (MatExp.expRemainderEntrywise sys.A Δt (m' + 2) (m' + 2)))
        (Zonotope.point u)).materialise.toSet := by
    rw [Zonotope.materialise_eq]
    exact Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) _ _
      (Set.mem_biUnion (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrixEntrywise _ hΔt
        (m' + 2) _ (Interval.mem_point sys.A) hWle ht0 htΔ) (Set.mem_image_of_mem _ hpt))
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
  show x t ∈ (Plus.plus (Plus.plus _ _) _ : PolyZonotope (Vec 𝕋 n)).toSet
  rw [hx]
  have hPU' : x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ uR) ∈
      (sys.inputSolutionEntrywiseFloat Δt (m' + 2) (MatExp.expRemainderEntrywise sys.A Δt (m' + 2)
        (m' + 2)) U).materialise.toSet := by
    rw [Zonotope.materialise_eq]; exact hPU
  have e1 := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hlinc hF)
  have e2 := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _
    (Set.add_mem_add e1 (Zonotope.ofIndep_outer _ hPU'))
  have e3 := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _
    (Set.add_mem_add e2 (Zonotope.ofIndep_outer _ hG))
  exact e3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
