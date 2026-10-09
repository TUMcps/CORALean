import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The input remainder's closed convex hull lies in the float product

The exact remainder `[-E(r)·r, E(r)·r]` of [1, Thm. 3.1], applied to the plain set `V.construct`
and closed and convexified as the exact theorem has it, sits inside the float product of
`intervalInputRemainder` with `V`: a matrix of the exact box is in the float one, so its image is
in the float product, and the float product is convex and closed, so the hull stays inside it.
Both `inputReach_subset_inputSolutionFloat` and the split of eq. (27) take their remainder from
here.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] noncomputable def aux_setMtimesIntervalRem :
    Mtimes (fun m k => Real.Interval (Mat ℝ m k)) (fun k => Set (Vec ℝ k)) where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_setMtimesIntervalRem


-- =======================================  MAIN THEOREM  ======================================= --

/-- The remainder's closed convex hull, inside the float product. -/
theorem LinearSys.inputRemainder_subset_float (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) (V : Zonotope 𝕋 n) :
    construct (Mtimes.mtimes (𝕄 := fun m k => Real.Interval (Mat ℝ m k))
      (S := fun k => Set (Vec ℝ k))
      (Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η)
      (V.construct : Set (Vec ℝ n)))
      ⊆ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V) := by -- --- PROOF ---
  set Z := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V
  refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_construct Z))
    (CompactSet.isClosed_construct Z)
  refine Set.iUnion₂_subset fun A hA => ?_
  exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct)
    (MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2
      (Interval.mem_point sys.A) hA)).trans
    (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := Zonotope 𝕋)
      (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
