module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionEntrywise
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `inputSolutionEntrywiseFloat` contains everything the input can contribute over a step

`inputReach_subset_inputSolutionEntrywise` [1] in floats, as `inputReach_subset_inputSolutionFloat`
has the scalar case: the exact theorem is taken at plain sets, and each set that run builds sits
inside the float one. An exact order's matrix is in `intervalInputTerm`'s box, and the remainder's
whole box in `intervalInputRemainderEntrywise`'s once the stored bound `W` holds `E(Δt,η)`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder
* `V` – input float zonotope

## Hypotheses
* `hΔt` – step length positive
* `hW` – the bound holds the exact remainder

## Conclusion
* the input reach of the zonotope over the step lies in the float input solution

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet ContSetLike Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] private def aux_setPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] private def aux_setMtimes : Mtimes (Mat ℝ) ExactSet where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.toSet_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified, so the
remainder's product is the closed convex set the exact theorem asks for. -/
@[reducible] private noncomputable def aux_setMtimesInterval :
    Mtimes ℐ ExactSet where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ toSet I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_setPlus aux_setMtimes aux_setMtimesInterval

/-- The exact orders, taken at plain sets, inside the float sum. -/
private theorem LinearSys.aux_inputTaylorSum_subset (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ i, toSet (sys.inputTaylorSum (S := ExactSet)
      (toReal r) V.toSet i) ⊆ (sys.inputTaylorSumFloat r V i).toSet := by -- --- PROOF ---
  -- order `i`'s matrix is in its float box, so its image is in the float product
  have hterm : ∀ i, (sys.inputTerm (toReal r) i *ᵥ ·) '' V.toSet
      ⊆ toSet (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (ContSet := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V) := by
    intro i
    have hM : sys.inputTerm (toReal r) i
        ∈ (MatExp.intervalInputTerm (Interval.point sys.A) r i).toSet :=
      MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i
    -- the float product holds the image under any member of the float box
    exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.toSet) hM).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V)
  intro i
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    exact (Set.add_subset_add ih (hterm (i + 1))).trans
      (Plus.plus_outer (sys.inputTaylorSumFloat r V i) _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputReach_subset_inputSolutionEntrywiseFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋}
    {η : ℕ} (hΔt : 0 < toReal Δt) (W : Mat 𝕋 n n)
    (hW : ∀ j k, Real.MatExp.expRemainderMat (Scalar.toRealMat sys.A) (toReal Δt) η j k
      ≤ toReal (W j k))
    (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    sys.inputReach (S := 𝒵[𝕋]) V (toReal Δt)
      ⊆ (sys.inputSolutionEntrywiseFloat Δt η W V).toSet := by -- --- PROOF ---
  -- the exact remainder's whole box is in the float one
  have hrem : toSet (Mtimes.mtimes (𝕄 := ℐ) (ContSet := ExactSet)
      (Real.MatExp.inputRemainderEntrywise (Scalar.toRealMat sys.A) (toReal Δt) η)
      (V.toSet : Set (Vec ℝ n)))
      ⊆ toSet (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalInputRemainderEntrywise Δt W) V) := by
    set Z := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
      (MatExp.intervalInputRemainderEntrywise Δt W) V
    -- the float box is closed and convex, so it suffices to hold each product of a member
    refine closure_minimal (convexHull_min ?_ (ConvexSet.convex_toSet Z))
      (CompactSet.isClosed_toSet Z)
    refine Set.iUnion₂_subset fun B hB => ?_
    -- a member of the exact box is in the float one, entry by entry
    have hBf : B ∈ (MatExp.intervalInputRemainderEntrywise Δt W).toSet := by
      refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
      obtain ⟨h1, h2⟩ := Real.Interval.mem_mat_iff.mp hB j k
      have hmul := mul_le_mulUp Δt (W j k)
      have hmul' : toReal Δt * Real.MatExp.expRemainderMat (Scalar.toRealMat sys.A) (toReal Δt)
          η j k ≤ toReal (mulUp Δt (W j k)) :=
        le_trans (mul_le_mul_of_nonneg_left (hW j k) hΔt.le) hmul
      simp only [Real.MatExp.inputRemainderEntrywise] at h1 h2
      simp only [MatExp.intervalInputRemainderEntrywise, Interval.nominal, RealImage.realImage,
        toRealMat, toReal_neg]
      constructor <;> linarith
    exact (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.toSet) hBf).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.intervalInputRemainderEntrywise Δt W) V)
  have hexact := sys.inputReach_subset_inputSolutionEntrywise (S := ExactSet) hΔt η
    (U := V.toSet) (ConvexSet.convex_toSet V) (CompactSet.isClosed_toSet V)
    (CompactSet.isBounded_toSet V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_toSet _).subset hrem)
  -- the exact set is the series plus the remainder, each inside the float one
  refine hexact.trans ?_
  unfold LinearSys.inputSolutionEntrywiseFloat LinearSys.inputSolutionEntrywise
  exact (Set.add_subset_add (sys.aux_inputTaylorSum_subset hΔt.le V η) hrem).trans
    (Plus.plus_outer (sys.inputTaylorSumFloat Δt V η) _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
