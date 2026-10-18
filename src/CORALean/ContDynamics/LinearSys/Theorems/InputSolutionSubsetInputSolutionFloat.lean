module

public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.RealMtimesIntervalMatSubset
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The float input solution holds the exact one

[1, Thm. 1]'s `⊕ᵢ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U` over `Real.Zonotope` is inside
`inputSolutionFloat` at a float zonotope holding `U`: order by order the exact matrix is in the
float interval matrix and `mtimes_outer` carries its image, the exact sums in `plus_outer`, and
the remainder is the exact zonotope map at the exact interval `[-E r, E r]`, inside the float
one by `Zonotope.real_mtimesIntervalMat_subset` since both ends of the exact interval are
matrices of the float one. The float zonotope has error box `{0}`, so its points are its nominal
part.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact orders, over `Real.Zonotope`, inside the float sum. -/
theorem LinearSys.aux_inputTaylorSumZ_subset (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {Wr : CORALean.Real.Zonotope (Vec ℝ n)} {V : Zonotope (Vec 𝕋 n)}
    (hW : Wr.construct ⊆ V.construct) : -- --- STMT ---
    ∀ i, construct (sys.inputTaylorSum (S := 𝒵)
        (toReal r) Wr i) ⊆ (sys.inputTaylorSumFloat r V i).construct := by -- --- PROOF ---
  -- order `i`'s matrix is in its float box, so the image of `Wr` is in the float product
  have hterm : ∀ i, construct (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) i) Wr)
      ⊆ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V).construct := by
    intro i y hy
    have hy' : y ∈ CORALean.Real.Zonotope.construct
        (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) i) Wr) := hy
    rw [← CORALean.Real.Zonotope.mtimes_exact] at hy'
    obtain ⟨u, hu, rfl⟩ := hy'
    exact Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm (Interval.point sys.A) r i) V
      (Set.mem_biUnion (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i)
        (Set.mem_image_of_mem _ (hW hu)))
  intro i
  -- the sum is the previous sum and one more order, each inside its float counterpart
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    intro y hy
    have hy' : y ∈ CORALean.Real.Zonotope.construct (CORALean.Real.Zonotope.plus
        (sys.inputTaylorSum (S := 𝒵) (toReal r) Wr i)
        (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) (i + 1)) Wr)) := hy
    rw [← CORALean.Real.Zonotope.plus_exact] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact Plus.plus_outer (sys.inputTaylorSumFloat r V i) _
      (Set.add_mem_add (ih ha) (hterm (i + 1) hb))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputSolution_subset_inputSolutionFloat (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.OrderAdmissibleFloat r r η)
    {Wr : CORALean.Real.Zonotope (Vec ℝ n)} {V : Zonotope (Vec 𝕋 n)}
    (hE : V.I_error = Interval.point fun _ => FloatOps.zero)
    (hW : Wr.construct ⊆ V.construct) : -- --- STMT ---
    construct (sys.inputSolution (S := 𝒵) (toReal r) η Wr)
      ⊆ (sys.inputSolutionFloat r η V).construct := by -- --- PROOF ---
  set IMr := CORALean.Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η with hIMr
  set IMf := MatExp.intervalInputRemainder (Interval.point sys.A) r η with hIMf
  intro y hy
  have hy' : y ∈ CORALean.Real.Zonotope.construct (CORALean.Real.Zonotope.plus
      (sys.inputTaylorSum (S := 𝒵) (toReal r) Wr η)
      (CORALean.Real.Zonotope.mtimesIntervalMat IMr Wr)) := hy
  rw [← CORALean.Real.Zonotope.plus_exact] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  -- the remainder's ends are matrices of the exact interval, so of the float one
  have hA : Scalar.toRealMat sys.A ∈ (Interval.point sys.A).construct :=
    Interval.mem_point sys.A
  -- the remainder's bound is nonnegative, so its interval has `inf ≤ sup`
  have hε : ‖toReal r • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2
  have hE0 := CORALean.Real.MatExp.expRemainderBound_nonneg η hε
  have hmem : ∀ M : Mat ℝ n n, (∀ i j, IMr.inf i j ≤ M i j ∧ M i j ≤ IMr.sup i j) →
      M ∈ IMf.construct := fun M hM =>
    MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2 hA
      (CORALean.Real.Interval.mem_mat_iff.mpr hM)
  have hle : ∀ i j, IMr.inf i j ≤ IMr.sup i j := fun _ _ => by
    show -(toReal r * CORALean.Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η)
      ≤ toReal r * CORALean.Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η
    nlinarith [mul_nonneg hr hE0]
  -- the remainder term, through the float interval-matrix product
  have hrem := Zonotope.real_mtimesIntervalMat_subset (IMf := IMf)
    (hmem _ fun i j => ⟨le_rfl, hle i j⟩) (hmem _ fun i j => ⟨hle i j, le_rfl⟩) hle hE hW hb
  have hrem' : b ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) IMf V).construct := by
    show b ∈ ((Zonotope.mtimesIntervalMat IMf V).materialise).construct
    rw [Zonotope.materialise_eq]
    exact hrem
  exact Plus.plus_outer (sys.inputTaylorSumFloat r V η) _
    (Set.add_mem_add (sys.aux_inputTaylorSumZ_subset hr hW η ha) hrem')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
