import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZonoFloat
import CORALean.ContDynamics.LinParamSys.Theorems.SmulPowMemInputTermZonoFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct

/-!
# `inputSolutionZonoFloat` holds every member's input contribution over a step

[1, Prop. 3.6] in floats, by way of the exact theorem at the frozen member, as
`inputReach_subset_inputSolutionFloat` takes it: `inputReach_subset_inputSolution` at plain
sets gives the member's orders `0 … η` and its remainder. Orders `0` and `1` then sit in
`inputTermZonoFloat` (`smul_pow_mem_inputTermZonoFloat`), orders from `2` in the interval
terms at `sys.A.interval`, and the remainder in `intervalInputRemainder` there; the
exact sum is regrouped as the float one is, Minkowski sums being associative.

`hη` is `OrderAdmissibleFloat` of the interval system `sys.A.interval` — a float check.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_zonoSetPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_zonoSetMtimes : Mtimes (Mat ℝ) (fun k => Set (Vec ℝ k)) where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] noncomputable def aux_zonoSetMtimesInterval :
    Mtimes (fun m k => Real.Interval (Mat ℝ m k)) (fun k => Set (Vec ℝ k)) where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_zonoSetPlus aux_zonoSetMtimes aux_zonoSetMtimesInterval

/-- One exact order's image inside the float product at a family that holds its matrix. -/
theorem LinParamSys.aux_image_subset_mtimes {𝕄 : ℕ → ℕ → Type}
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [Mtimes 𝕄 (Zonotope 𝕋)] {M : Mat ℝ n n} {X : 𝕄 n n}
    (hM : M ∈ construct X) (V : Zonotope 𝕋 n) :
    (M *ᵥ ·) '' V.construct ⊆ construct (Mtimes.mtimes X V) :=
  (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct) hM).trans
    (Mtimes.mtimes_outer (S := Zonotope 𝕋) X V)

/-- The member's exact orders `0 … m + 2`, regrouped as the float sum is: orders `0` and
`1` through the matrix zonotope, then the interval tail. -/
theorem LinParamSys.aux_inputTaylorSum_subset_zono
    (sys : LinParamSys (fun m n => MatZonotope 𝕋 m n) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope 𝕋 n) :
    ∀ m, construct ((LinearSys.mk A : LinearSys ℝ n).inputTaylorSum
      (S := fun k => Set (Vec ℝ k)) (toReal r) V.construct (m + 2))
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n)
          (sys.inputTermZonoFloat r 0) V ⊞
          Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n) (sys.inputTermZonoFloat r 1) V)
        + construct ((LinParamSys.mk (𝕄 := fun m n => Interval (Mat 𝕋 m n))
            sys.A.interval).inputTaylorSumTailFloat r V (m + 2)) := by -- --- PROOF ---
  have hAI : A ∈ sys.A.interval.construct := MatZonotope.interval_contains _ hA
  -- orders `0` and `1`, through the matrix zonotope
  have hZ : ∀ i, ((LinearSys.mk A : LinearSys ℝ n).inputTerm (toReal r) i *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n)
        (sys.inputTermZonoFloat r i) V) :=
    fun i => LinParamSys.aux_image_subset_mtimes
      (sys.smul_pow_mem_inputTermZonoFloat hr hA i) V
  -- every later order, through the interval matrix the zonotope encloses
  have hI : ∀ i, ((LinearSys.mk A : LinearSys ℝ n).inputTerm (toReal r) i *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (MatExp.intervalInputTerm sys.A.interval r i) V) :=
    fun i => LinParamSys.aux_image_subset_mtimes
      (MatExp.smul_pow_mem_intervalInputTerm _ hr hAI i) V
  have h01 := (Set.add_subset_add (hZ 0) (hZ 1)).trans (Plus.plus_outer
    (Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n) (sys.inputTermZonoFloat r 0) V)
    (Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n) (sys.inputTermZonoFloat r 1) V))
  intro m
  induction m with
  | zero => exact Set.add_subset_add h01 (hI 2)
  -- the next order joins the tail, by associativity and the tail's own `plus`
  | succ m ih =>
    refine (Set.add_subset_add ih (hI (m + 3))).trans ?_
    rw [add_assoc]
    exact Set.add_subset_add le_rfl (Plus.plus_outer ((LinParamSys.mk (𝕄 := fun m n =>
      Interval (Mat 𝕋 m n)) sys.A.interval).inputTaylorSumTailFloat r V (m + 2))
      (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (MatExp.intervalInputTerm sys.A.interval r (m + 3)) V))

/-- The member's remainder, closed and convexified, inside the float product. -/
theorem LinParamSys.aux_inputRemainder_subset_zono
    (sys : LinParamSys (fun m n => MatZonotope 𝕋 m n) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {η : ℕ} (hη : (LinParamSys.mk (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      sys.A.interval).OrderAdmissibleFloat r r η)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope 𝕋 n) :
    construct (Mtimes.mtimes (𝕄 := fun m k => Real.Interval (Mat ℝ m k))
      (S := fun k => Set (Vec ℝ k)) (Real.MatExp.inputRemainder A (toReal r) η)
      (V.construct : Set (Vec ℝ n)))
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (MatExp.intervalInputRemainder sys.A.interval r η) V) := by -- --- PROOF ---
  set Z := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (MatExp.intervalInputRemainder sys.A.interval r η) V
  refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_construct Z))
    (CompactSet.isClosed_construct Z)
  refine Set.iUnion₂_subset fun M hM => ?_
  exact LinParamSys.aux_image_subset_mtimes (MatExp.inputRemainder_subset_intervalInputRemainder
    _ hr η hη.2 (MatZonotope.interval_contains _ hA) hM) V


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an input in `V` contributes over `[0, Δt]` at a member `A ∈ sys.A`
lies in `inputSolutionZonoFloat`. -/
theorem LinParamSys.inputReach_subset_inputSolutionZonoFloat
    (sys : LinParamSys (fun m n => MatZonotope 𝕋 m n) n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : (LinParamSys.mk (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      sys.A.interval).OrderAdmissibleFloat Δt Δt η)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope 𝕋 n) :
    (LinearSys.mk A : LinearSys ℝ n).inputReach (S := Zonotope 𝕋) V (toReal Δt)
      ⊆ (sys.inputSolutionZonoFloat Δt η V).construct := by -- --- PROOF ---
  -- the float bound's condition is the exact one's, with room to spare
  have hε : ‖toReal Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound sys.A.interval Δt
      (MatZonotope.interval_contains _ hA)
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt sys.A.interval))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  have hrem := sys.aux_inputRemainder_subset_zono hΔt.le hη hA V
  have hexact := (LinearSys.mk A : LinearSys ℝ n).inputReach_subset_inputSolution
    (S := fun k => Set (Vec ℝ k)) hΔt η hε
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
