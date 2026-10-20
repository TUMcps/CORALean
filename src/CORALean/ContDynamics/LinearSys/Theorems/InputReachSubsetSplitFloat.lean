module

public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputRemainderSubsetFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputTaylorSumTailSubsetFloat

@[expose] public section

/-!
# The input's share over a step lies in `bPU_0 ⊕ bPU_∞`

[1, Alg. 2] eq. (27) splits the particular solution `bPU(Δt)` into `bPU_0(Δt) = Δt·U₀`, the
order `0`, and `bPU_∞(Δt)`, orders `1 … η` and the remainder, so that line 18 accumulates the
first and line 17 boxes the second. Everything an input in `V` contributes over a step of
length `Δt` is in the sum of the two float sets, in that split: the exact orders are
`inputTaylorSum`, whose order `0` comes off at the front and whose rest is `inputTaylorSumTail`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `V` – input float zonotope

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible

## Conclusion
* the input reach lies in the first-order term plus the Taylor tail and remainder in floats

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_setPlusSplit (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_setMtimesSplit : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified. -/
@[reducible] noncomputable def aux_setMtimesIntervalSplit :
    Mtimes ℐ 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] aux_setPlusSplit aux_setMtimesSplit aux_setMtimesIntervalSplit

/-- From order `1` on, the exact sum is order `0` and the exact tail. -/
theorem LinearSys.aux_inputTaylorSum_eq_term_add_tail (sys : LinearSys 𝕋 n) (r : ℝ)
    (U : Set (Vec ℝ n)) (m : ℕ) : -- --- CONCL ---
    sys.inputTaylorSum (S := 𝒮) r U (m + 1)
      = (sys.inputTerm r 0 *ᵥ ·) '' U
        + sys.inputTaylorSumTail (S := 𝒮) r U (m + 1) := by -- --- PROOF ---
  induction m with
  | zero => rfl
  | succ m ih =>
    show sys.inputTaylorSum (S := 𝒮) r U (m + 1)
        + (sys.inputTerm r (m + 2) *ᵥ ·) '' U
      = (sys.inputTerm r 0 *ᵥ ·) '' U
        + (sys.inputTaylorSumTail (S := 𝒮) r U (m + 1)
          + (sys.inputTerm r (m + 2) *ᵥ ·) '' U)
    rw [ih, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputReach_subset_split_float (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η)
    (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    sys.inputReach (S := 𝒵[𝕋]) V (toReal Δt)
      ⊆ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
          (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V).construct
        + (sys.inputTaylorSumTailFloat Δt V η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
          (𝕄 := ℐ[𝕋]) (MatExp.intervalInputRemainder
            (Interval.point sys.A) Δt η) V).construct := by -- --- PROOF ---
  have hε : ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point sys.A) Δt
      (Interval.mem_point sys.A)
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A)))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  -- the exact theorem at plain sets, its remainder inside the float product
  have hrem := sys.inputRemainder_subset_float hΔt.le hη V
  have hexact := sys.inputReach_subset_inputSolution (S := 𝒮) hΔt η hε
    (U := V.construct) (ConvexSet.convex_construct V) (CompactSet.isClosed_construct V)
    (CompactSet.isBounded_construct V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_construct _).subset hrem)
  -- order `0`'s matrix is in its float box, so its image is in the float product
  have hterm0 : (sys.inputTerm (toReal Δt) 0 *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V) :=
    (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct)
      (MatExp.smul_pow_mem_intervalInputTerm _ hΔt.le (Interval.mem_point sys.A) 0)).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V)
  -- from order `1` on, the exact sum is order `0` and the exact tail, and the float sets hold both
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 1 := ⟨η - 1, by have := hη.1; omega⟩
  refine hexact.trans ?_
  unfold LinearSys.inputSolution
  show sys.inputTaylorSum (S := 𝒮) (toReal Δt) V.construct (m + 1) + _ ⊆ _
  rw [sys.aux_inputTaylorSum_eq_term_add_tail, add_assoc]
  exact Set.add_subset_add hterm0 ((Set.add_subset_add
    (sys.inputTaylorSumTail_subset_float hΔt.le V (m + 1)) hrem).trans
    (Plus.plus_outer (sys.inputTaylorSumTailFloat Δt V (m + 1)) _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
