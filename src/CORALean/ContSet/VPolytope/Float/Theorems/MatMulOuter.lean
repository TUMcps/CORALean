module

public import CORALean.ContSet.VPolytope.Float.Operations.MatMul
public import CORALean.ContSet.Conversion.Float.Theorems.VPolytopeIntervalMatrixContains
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset

@[expose] public section

/-!
# `VPolytope.matMul` contains the products of the members

A member is a nominal point plus a point of the error box. The product of two nominal points is in
the hull of the exact vertex products, which differ from the stored ones by a residual in
`step_matColumnGap`; the cross terms `a f + e (b + f)` are interval products of boxes that contain
their factors. The sum of the residual and the cross terms is in the stored error box.

## Inputs
* `P` – first matrix polytope
* `Q` – second matrix polytope
* `A` – member of `P`
* `B` – member of `Q`

## Hypotheses
* `hA` – `A` lies in `P`
* `hB` – `B` lies in `Q`

## Conclusion
* `A * B` lies in the product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix between the two roundings of vertex `l` is within the gap of the lower one. -/
private theorem VPolytope.aux_mem_matColumnGap {k : ℕ} {lo hi : Fin k → Mat 𝕋 p r}
    {A : Mat ℝ p r} {l : Fin k}
    (h : ∀ i j, toReal (lo l i j) ≤ A i j ∧ A i j ≤ toReal (hi l i j)) : -- --- CONCL ---
    (fun i j => A i j - toReal (lo l i j)) ∈
      (VPolytope.step_matColumnGap lo hi).construct := by -- --- PROOF ---
  -- the residual is nonnegative, and below the gap of its own vertex, hence of the widest
  refine Interval.mem_mat_iff.mpr fun i j => ⟨?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ A i j - toReal (lo l i j)
    rw [toReal_zero]
    linarith [(h i j).1]
  · show A i j - toReal (lo l i j) ≤ toReal (maximumOver fun l' => subUp (hi l' i j) (lo l' i j))
    calc A i j - toReal (lo l i j)
        ≤ toReal (hi l i j) - toReal (lo l i j) := by linarith [(h i j).2]
      _ ≤ toReal (subUp (hi l i j) (lo l i j)) := sub_le_subUp _ _
      _ ≤ toReal (maximumOver fun l' => subUp (hi l' i j) (lo l' i j)) :=
          le_maximumOver (fun l' => subUp (hi l' i j) (lo l' i j)) l


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.matMul_outer (P : VPolytope (Mat 𝕋 p q)) (Q : VPolytope (Mat 𝕋 q r))
    {A : Mat ℝ p q} {B : Mat ℝ q r} (hA : A ∈ InflatedContSet.construct P)
    (hB : B ∈ InflatedContSet.construct Q) : -- --- CONCL ---
    A * B ∈ InflatedContSet.construct (P.matMul Q) := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hA
  obtain ⟨b, hb, f, hf, rfl⟩ := hB
  -- the nominal product is in the hull of the exact vertex products
  have hab := Real.VPolytope.matMul_outer P.nominal Q.nominal ha hb
  -- which sit within the gap box of the stored, rounded-down ones
  have hgap : (Real.VPolytope.matMul P.nominal Q.nominal).construct ⊆
      InflatedContSet.nominalSet (P.matMul Q) + (VPolytope.step_matColumnGap
        (fun l => matMulDown (P.V (finProdFinEquiv.symm l).1) (Q.V (finProdFinEquiv.symm l).2))
        (fun l => matMulUp (P.V (finProdFinEquiv.symm l).1) (Q.V (finProdFinEquiv.symm l).2))
          ).construct := by
    refine Real.VPolytope.construct_subset_add _ _ (Real.Interval.convex_construct _) fun l => ?_
    refine VPolytope.aux_mem_matColumnGap fun i j => ?_
    -- one exact product of stored matrices, between its two directed roundings
    have key : ∀ (X : Mat 𝕋 p q) (Y : Mat 𝕋 q r),
        toReal (matMulDown X Y i j) ≤ matMulBilin (toRealMat X) (toRealMat Y) i j ∧
          matMulBilin (toRealMat X) (toRealMat Y) i j ≤ toReal (matMulUp X Y i j) := by
      intro X Y
      rw [matMulBilin_apply, Matrix.mul_apply]
      exact ⟨dotDown_le (X i) (fun l => Y l j), le_dotUp (X i) (fun l => Y l j)⟩
    exact key _ _
  obtain ⟨m, hm, g, hg, hmg⟩ := hgap hab
  -- the cross terms: `a` is in the box of the nominal vertices, `b + f` in that of `Q`
  have hzero : (0 : Mat ℝ p q) ∈
      (Interval.point (α := Mat 𝕋 p q) fun _ _ => (zero : 𝕋)).construct :=
    Interval.mem_mat_iff.mpr fun i j => by
      show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
      rw [toReal_zero]
      exact ⟨le_rfl, le_rfl⟩
  have ha' : a ∈ ({ P with I_error := Interval.point fun _ _ => zero } :
      VPolytope (Mat 𝕋 p q)).intervalMatrix.construct :=
    VPolytope.intervalMatrix_contains _ ⟨a, ha, 0, hzero, add_zero a⟩
  have hb' : b + f ∈ Q.intervalMatrix.construct :=
    VPolytope.intervalMatrix_contains Q ⟨b, hb, f, hf, rfl⟩
  have hE := Interval.matPlus_outer _ _ (Interval.matMul_outer _ _ ha' hf)
    (Interval.matMul_outer _ _ he hb')
  -- the residual and the cross terms together are in the stored error box
  have hI := Interval.matPlus_outer _ _ hg hE
  refine ⟨m, hm, g + (a * f + e * (b + f)), hI, ?_⟩
  -- `(a + e)(b + f) = a b + (a f + e (b + f))`
  have heq : (a + e) * (b + f) = a * b + (a * f + e * (b + f)) := by
    rw [Matrix.add_mul, Matrix.mul_add a b f, add_assoc]
  have hmg' : m + g = a * b := hmg
  rw [heq, ← hmg', add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
