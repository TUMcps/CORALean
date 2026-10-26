module

public import CORALean.ContDynamics.LinParamSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZonoFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeMatIntervalContains

@[expose] public section

/-!
# `inputSolutionZonoFloat` holds every member's input contribution over a step

[1, Thm. 1] in floats, by way of the exact theorem at the frozen member, as
`inputReach_subset_inputSolutionFloat` takes it: `inputReach_subset_inputSolution` at plain
sets gives the member's orders `0 … η` and its remainder. Orders `0` and `1` then sit in
`inputTermZonoFloat` (`aux_smul_pow_mem_inputTermZonoFloat`), orders from `2` in the interval
terms at `sys.A.matInterval`, and the remainder in `intervalInputRemainder` there; the
exact sum is regrouped as the float one is, Minkowski sums being associative.

`hη` is `IsOrderAdmissibleFloat` of the interval system `sys.A.matInterval` — a float check.

## Inputs
* `sys` – system
* `Δt` – step size
* `η` – Taylor order
* `A` – system matrix member
* `V` – input zonotope

## Hypotheses
* `hΔt` – step positive
* `hη` – order admissible
* `hA` – `A` lies in the matrix zonotope

## Conclusion
* everything the input contributes over the step lies in the enclosure

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A member's order-`i` input matrix lies in `inputTermZonoFloat`. -/
private theorem LinParamSys.aux_smul_pow_mem_inputTermZonoFloat
    (sys : LinParamSys 𝕄𝒵[𝕋] n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (i : ℕ) : -- --- CONCL ---
    (toReal r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i
      ∈ (sys.inputTermZonoFloat r i).construct := by -- --- PROOF ---
  show _ ∈ (Zonotope.matSmul _ _ (sys.A.matPow i)).materialiseMat.construct
  rw [Zonotope.materialiseMat_eq]
  exact Zonotope.matSmul_outer (MatExp.taylorCoeffBounds_mem hr (i + 1)).1
    (MatExp.taylorCoeffBounds_mem hr (i + 1)).2 _ (Zonotope.matPow_outer sys.A hA i)


/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] private def aux_zonoSetPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] private def aux_zonoSetMtimes : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] private noncomputable def aux_zonoSetMtimesInterval :
    Mtimes ℐ 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_zonoSetPlus aux_zonoSetMtimes aux_zonoSetMtimesInterval

/-- One exact order's image inside the float product at a family that holds its matrix. -/
private theorem LinParamSys.aux_image_subset_mtimes {𝕄 : ℕ → ℕ → Type}
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [Mtimes 𝕄 𝒵[𝕋]]
    {M : Mat ℝ n n} {X : 𝕄 n n}
    (hM : M ∈ construct X) (V : Zonotope (Vec 𝕋 n)) :
    (M *ᵥ ·) '' V.construct ⊆ construct (Mtimes.mtimes (S := 𝒵[𝕋]) X V) :=
  (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct) hM).trans
    (Mtimes.mtimes_outer (S := 𝒵[𝕋]) X V)

/-- The member's exact orders `0 … m + 2`, regrouped as the float sum is: orders `0` and
`1` through the matrix zonotope, then the interval tail. -/
private theorem LinParamSys.aux_inputTaylorSum_subset_zono
    (sys : LinParamSys 𝕄𝒵[𝕋] n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ m, construct ((LinearSys.canonical A : LinearSys ℝ n).inputTaylorSum
      (S := 𝒮) (toReal r) V.construct (m + 2))
      ⊆ construct (Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋])
        (S := 𝒵[𝕋])
          (sys.inputTermZonoFloat r 0) V ⊞
          Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
            (sys.inputTermZonoFloat r 1) V)
        + construct ((LinParamSys.canonical (𝕄 := ℐ[𝕋])
            sys.A.matInterval).inputTaylorSumTailFloat r V (m + 2)) := by -- --- PROOF ---
  have hAI : A ∈ sys.A.matInterval.construct := Zonotope.matInterval_contains _ hA
  -- orders `0` and `1`, through the matrix zonotope
  have hZ : ∀ i, ((LinearSys.canonical A : LinearSys ℝ n).inputTerm (toReal r) i *ᵥ ·) ''
      V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋])
        (S := 𝒵[𝕋])
        (sys.inputTermZonoFloat r i) V) :=
    fun i => LinParamSys.aux_image_subset_mtimes
      (sys.aux_smul_pow_mem_inputTermZonoFloat hr hA i) V
  -- every later order, through the interval matrix the zonotope encloses
  have hI : ∀ i, ((LinearSys.canonical A : LinearSys ℝ n).inputTerm (toReal r) i *ᵥ ·) ''
      V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm sys.A.matInterval r i) V) :=
    fun i => LinParamSys.aux_image_subset_mtimes
      (MatExp.smul_pow_mem_intervalInputTerm _ hr hAI i) V
  have h01 := (Set.add_subset_add (hZ 0) (hZ 1)).trans (Plus.plus_outer
    (Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
      (sys.inputTermZonoFloat r 0) V)
    (Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
      (sys.inputTermZonoFloat r 1) V))
  intro m
  induction m with
  | zero => exact Set.add_subset_add h01 (hI 2)
  -- the next order joins the tail, by associativity and the tail's own `plus`
  | succ m ih =>
    refine (Set.add_subset_add ih (hI (m + 3))).trans ?_
    rw [add_assoc]
    exact Set.add_subset_add le_rfl (Plus.plus_outer ((LinParamSys.canonical (𝕄 := fun m n =>
      Interval (Mat 𝕋 m n)) sys.A.matInterval).inputTaylorSumTailFloat r V (m + 2))
      (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm sys.A.matInterval r (m + 3)) V))

/-- The member's remainder, closed and convexified, inside the float product. -/
private theorem LinParamSys.aux_inputRemainder_subset_zono
    (sys : LinParamSys 𝕄𝒵[𝕋] n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {η : ℕ} (hη : (LinParamSys.canonical (𝕄 := ℐ[𝕋])
      sys.A.matInterval).IsOrderAdmissibleFloat r r η)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    construct (Mtimes.mtimes (𝕄 := ℐ)
      (S := 𝒮) (Real.MatExp.inputRemainder A (toReal r) η)
      (V.construct : Set (Vec ℝ n)))
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputRemainder sys.A.matInterval r η) V) := by -- --- PROOF ---
  set Z := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (MatExp.intervalInputRemainder sys.A.matInterval r η) V
  refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_construct Z))
    (CompactSet.isClosed_construct Z)
  refine Set.iUnion₂_subset fun M hM => ?_
  exact LinParamSys.aux_image_subset_mtimes (MatExp.inputRemainder_subset_intervalInputRemainder
    _ hr η hη.2 (Zonotope.matInterval_contains _ hA) hM) V


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an input in `V` contributes over `[0, Δt]` at a member `A ∈ sys.A`
lies in `inputSolutionZonoFloat`. -/
theorem LinParamSys.inputReach_subset_inputSolutionZonoFloat
    (sys : LinParamSys 𝕄𝒵[𝕋] n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : (LinParamSys.canonical (𝕄 := ℐ[𝕋])
      sys.A.matInterval).IsOrderAdmissibleFloat Δt Δt η)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒵[𝕋]) V (toReal Δt)
      ⊆ (sys.inputSolutionZonoFloat Δt η V).construct := by -- --- PROOF ---
  -- the float bound's condition is the exact one's, with room to spare
  have hε : ‖toReal Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound sys.A.matInterval Δt
      (Zonotope.matInterval_contains _ hA)
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt sys.A.matInterval))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  have hrem := sys.aux_inputRemainder_subset_zono hΔt.le hη hA V
  have hexact := (LinearSys.canonical A : LinearSys ℝ n).inputReach_subset_inputSolution
    (S := 𝒮) hΔt η hε
    (U := V.construct) (ConvexSet.convex_construct V) (CompactSet.isClosed_construct V)
    (CompactSet.isBounded_construct V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_construct _).subset hrem)
  refine hexact.trans ?_
  have h2 := hη.1
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 2 := ⟨η - 2, by omega⟩
  -- the three Taylor pieces, then the remainder, each `plus` absorbing the next
  refine (Set.add_subset_add ((sys.aux_inputTaylorSum_subset_zono hΔt.le hA V m).trans
    (Plus.plus_outer _ _)) hrem).trans (Plus.plus_outer _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
