module

public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputRemainderSubsetFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `inputSolutionFloat` contains everything the input can contribute over a step

[1, Thm. 1] in floats, by way of the exact theorem rather than a second proof
of it: `inputReach_subset_inputSolution` is generic over the representation, so
it is taken at plain sets — Minkowski sum, image, and for an interval matrix the
closed convex hull of the images — where it asks nothing a float zonotope cannot
give. Each set that run builds then sits inside the float one: an exact order's
matrix is in `intervalInputTerm`'s box, the remainder's whole box in
`intervalInputRemainder`'s, and a float product is convex and closed, so the
hull the remainder took stays inside it.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `V` – input float zonotope

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible

## Conclusion
* the input reach of the zonotope over the step lies in the float input solution

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
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

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_setPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_setMtimes : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] noncomputable def aux_setMtimesInterval :
    Mtimes ℐ 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_setPlus aux_setMtimes aux_setMtimesInterval

/-- The exact orders, taken at plain sets, inside the float sum. -/
theorem LinearSys.aux_inputTaylorSum_subset (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ i, construct (sys.inputTaylorSum (S := 𝒮)
      (toReal r) V.construct i) ⊆ (sys.inputTaylorSumFloat r V i).construct := by -- --- PROOF ---
  -- order `i`'s matrix is in its float box, so its image is in the float product
  have hterm : ∀ i, (sys.inputTerm (toReal r) i *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V) := by
    intro i
    have hM : sys.inputTerm (toReal r) i
        ∈ (MatExp.intervalInputTerm (Interval.point sys.A) r i).construct :=
      MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i
    exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct) hM).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V)
  intro i
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    exact (Set.add_subset_add ih (hterm (i + 1))).trans
      (Plus.plus_outer (sys.inputTaylorSumFloat r V i) _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputReach_subset_inputSolutionFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η)
    (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    sys.inputReach (S := 𝒵[𝕋]) V (toReal Δt)
      ⊆ (sys.inputSolutionFloat Δt η V).construct := by -- --- PROOF ---
  -- the float bound's condition is the exact one's, with room to spare
  have hε : ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point sys.A) Δt
      (Interval.mem_point sys.A)
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A)))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  have hrem := sys.inputRemainder_subset_float hΔt.le hη V
  have hexact := sys.inputReach_subset_inputSolution (S := 𝒮) hΔt η hε
    (U := V.construct) (ConvexSet.convex_construct V) (CompactSet.isClosed_construct V)
    (CompactSet.isBounded_construct V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_construct _).subset hrem)
  refine hexact.trans ?_
  unfold LinearSys.inputSolutionFloat
  exact (Set.add_subset_add (sys.aux_inputTaylorSum_subset hΔt.le V η) hrem).trans
    (Plus.plus_outer (sys.inputTaylorSumFloat Δt V η) _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
