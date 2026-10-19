module

public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The input remainder's closed convex hull lies in the float product

The exact remainder `[-E(r)·r, E(r)·r]` of [1, Thm. 1], applied to the plain set `V.construct`
and closed and convexified as the exact theorem has it, sits inside the float product of
`intervalInputRemainder` with `V`: a matrix of the exact box is in the float one, so its image is
in the float product, and the float product is convex and closed, so the hull stays inside it.
Both `inputReach_subset_inputSolutionFloat` and the split of eq. (27) take their remainder from
here.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
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

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] noncomputable def aux_setMtimesIntervalRem :
    Mtimes ℐ 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_setMtimesIntervalRem


-- =======================================  MAIN THEOREM  ======================================= --

/-- The remainder's closed convex hull, inside the float product. -/
theorem LinearSys.inputRemainder_subset_float (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    construct (Mtimes.mtimes (𝕄 := ℐ)
      (S := 𝒮)
      (Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η)
      (V.construct : Set (Vec ℝ n)))
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V) := by -- --- PROOF ---
  set Z := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V
  refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_construct Z))
    (CompactSet.isClosed_construct Z)
  refine Set.iUnion₂_subset fun A hA => ?_
  exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct)
    (MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2
      (Interval.mem_point sys.A) hA)).trans
    (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
