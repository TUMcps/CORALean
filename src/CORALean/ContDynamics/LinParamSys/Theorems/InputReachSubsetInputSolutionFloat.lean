import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct

/-!
# `inputSolutionFloat` holds every member's input contribution over a step

[1, Thm. 3.1] in floats at a set-valued matrix, by way of the exact theorem at
the frozen member, as `LinearSys.inputReach_subset_inputSolutionFloat` takes it
at the stored one. `inputReach_subset_inputSolution` is generic over the
representation, so it is taken at plain sets; each of their pieces then sits in
the float one, because the member's order-`i` matrix is in
`intervalInputTerm sys.A` and its remainder box in `intervalInputRemainder sys.A`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_paramSetPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_paramSetMtimes : Mtimes (Mat ℝ) (fun k => Set (Vec ℝ k)) where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] noncomputable def aux_paramSetMtimesInterval :
    Mtimes (fun m k => Real.Interval (Mat ℝ m k)) (fun k => Set (Vec ℝ k)) where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_paramSetPlus aux_paramSetMtimes aux_paramSetMtimesInterval

/-- The member's exact orders, taken at plain sets, inside the float sum. -/
theorem LinParamSys.aux_inputTaylorSum_subset
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (V : Zonotope (Vec 𝕋 n)) :
    ∀ i, construct ((LinearSys.mk A : LinearSys ℝ n).inputTaylorSum
      (S := fun k => Set (Vec ℝ k)) (toReal r) V.construct i)
      ⊆ (sys.inputTaylorSumFloat r V i).construct := by -- --- PROOF ---
  -- order `i`'s matrix is in its float box, so its image is in the float product
  have hterm : ∀ i, ((LinearSys.mk A : LinearSys ℝ n).inputTerm (toReal r) i *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalInputTerm sys.A r i) V) := by
    intro i
    have hM : (LinearSys.mk A : LinearSys ℝ n).inputTerm (toReal r) i
        ∈ (MatExp.intervalInputTerm sys.A r i).construct :=
      MatExp.smul_pow_mem_intervalInputTerm _ hr hA i
    exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct) hM).trans
      (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalInputTerm sys.A r i) V)
  intro i
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    exact (Set.add_subset_add ih (hterm (i + 1))).trans
      (Plus.plus_outer (sys.inputTaylorSumFloat r V i) _)

/-- The member's remainder, closed and convexified, inside the float product. -/
theorem LinParamSys.aux_inputRemainder_subset
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) {A : Mat ℝ n n} (hA : A ∈ sys.A.construct)
    (V : Zonotope (Vec 𝕋 n)) :
    construct (Mtimes.mtimes (𝕄 := fun m k => Real.Interval (Mat ℝ m k))
      (S := fun k => Set (Vec ℝ k)) (Real.MatExp.inputRemainder A (toReal r) η)
      (V.construct : Set (Vec ℝ n)))
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalInputRemainder sys.A r η) V) := by -- --- PROOF ---
  set Z := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalInputRemainder sys.A r η) V
  refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_construct Z))
    (CompactSet.isClosed_construct Z)
  refine Set.iUnion₂_subset fun M hM => ?_
  exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct)
    (MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2 hA hM)).trans
    (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputRemainder sys.A r η) V)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an input in `V` contributes over `[0, Δt]` at a member `A ∈ sys.A`
lies in `inputSolutionFloat`. -/
theorem LinParamSys.inputReach_subset_inputSolutionFloat
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) {A : Mat ℝ n n}
    (hA : A ∈ sys.A.construct) (V : Zonotope (Vec 𝕋 n)) :
    (LinearSys.mk A : LinearSys ℝ n).inputReach (S := fun k => Zonotope (Vec 𝕋 k)) V (toReal Δt)
      ⊆ (sys.inputSolutionFloat Δt η V).construct := by -- --- PROOF ---
  -- the float bound's condition is the exact one's, with room to spare
  have hε : ‖toReal Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound sys.A Δt hA
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt sys.A))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  have hrem := sys.aux_inputRemainder_subset hΔt.le hη hA V
  have hexact := (LinearSys.mk A : LinearSys ℝ n).inputReach_subset_inputSolution
    (S := fun k => Set (Vec ℝ k)) hΔt η hε
    (U := V.construct) (ConvexSet.convex_construct V) (CompactSet.isClosed_construct V)
    (CompactSet.isBounded_construct V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_construct _).subset hrem)
  refine hexact.trans ?_
  unfold LinParamSys.inputSolutionFloat
  exact (Set.add_subset_add (sys.aux_inputTaylorSum_subset hΔt.le hA V η) hrem).trans
    (Plus.plus_outer (sys.inputTaylorSumFloat Δt V η) _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
